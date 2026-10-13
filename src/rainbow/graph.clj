(ns rainbow.graph
  "Pure content-addressed graph for checked declarations, claims, proofs, and attempts."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.term :as term]))

(def schema-version 1)

(defn empty-graph []
  {:rainbow/kind :proof-graph
   :graph/schema-version schema-version
   :graph/nodes {}
   :graph/edges #{}
   :graph/aliases {}})

(defn claim-content [declaration]
  {:rainbow/kind :claim
   :claim/type (:rainbow/type declaration)
   :claim/universes (:rainbow/universes declaration)
   :claim/dependencies (term/constants (:rainbow/type declaration))
   :claim/schema-version 1})

(defn claim-id [declaration]
  (canonical/content-id (claim-content declaration)))

(defn proof-content [declaration]
  {:rainbow/kind :proof
   :proof/claim-id (claim-id declaration)
   :proof/term (:rainbow/value declaration)
   :proof/dependencies (:rainbow/dependencies declaration)
   :proof/axioms (:rainbow/axioms declaration)
   :proof/schema-version 1})

(defn proof-id [declaration]
  (canonical/content-id (proof-content declaration)))

(defn foreign-object-content
  "Semantic content retained from a foreign exporter without translating it
  into a native declaration. Unsupported, unsafe, and partial objects may be
  indexed here; this function does not make them kernel-usable."
  [object]
  (select-keys object
               [:rainbow/kind :foreign/schema-version :foreign/system
                :foreign/version :foreign/commit :foreign/name :foreign/kind
                :foreign/universes :foreign/raw-type :foreign/raw-value
                :foreign/unsafe? :foreign/partial? :foreign/dependencies
                :foreign/attributes :foreign/source :foreign/error]))

(defn foreign-object-id [object]
  (canonical/content-id (foreign-object-content object)))

(defn foreign-reference-content [system version commit name]
  {:rainbow/kind :foreign-reference
   :foreign/system system
   :foreign/version version
   :foreign/commit commit
   :foreign/name name})

(defn foreign-reference-id [system version commit name]
  (canonical/content-id
   (foreign-reference-content system version commit name)))

(defn- node-semantic-content [node]
  (case (:graph.node/kind node)
    :declaration (environment/semantic-declaration (:graph.node/declaration node))
    :claim (:graph.node/claim node)
    :proof (:graph.node/proof node)
    :foreign-declaration (foreign-object-content (:graph.node/foreign-object node))
    :foreign-reference (:graph.node/foreign-reference node)
    :attempt (dissoc (:graph.node/attempt node) :cost)
    :run (dissoc (:graph.node/run node) :run/id)
    :goal-reference {:rainbow/kind :goal-reference
                     :goal/hash (:graph.node/id node)}))

(defn- expected-node-id [node]
  (case (:graph.node/kind node)
    :declaration (environment/declaration-id (:graph.node/declaration node))
    :claim (canonical/content-id (:graph.node/claim node))
    :proof (canonical/content-id (:graph.node/proof node))
    :foreign-declaration (foreign-object-id (:graph.node/foreign-object node))
    :foreign-reference (canonical/content-id (:graph.node/foreign-reference node))
    :attempt (canonical/content-id (dissoc (:graph.node/attempt node)
                                           :attempt/id :cost))
    :run (canonical/content-id (dissoc (:graph.node/run node) :run/id))
    :goal-reference (:graph.node/id node)))

(defn- put-node [graph node]
  (let [id (:graph.node/id node)
        expected (expected-node-id node)
        existing (get-in graph [:graph/nodes id])]
    (when-not (= id expected)
      (throw (ex-info "Graph node ID does not match semantic content"
                      {:error/category :graph/node-id-mismatch
                       :id id :expected expected :kind (:graph.node/kind node)})))
    (when (and existing
               (not= (node-semantic-content existing) (node-semantic-content node)))
      (throw (ex-info "Conflicting graph node content"
                      {:error/category :graph/node-conflict :id id})))
    (assoc-in graph [:graph/nodes id] (or existing node))))

(defn- put-edge [graph from relation to]
  (update graph :graph/edges conj [from relation to]))

(defn add-declaration [graph declaration]
  (let [declaration-id (:rainbow/id declaration)
        declaration-node {:graph.node/id declaration-id
                          :graph.node/kind :declaration
                          :graph.node/declaration declaration}
        graph (put-node graph declaration-node)
        graph (reduce (fn [current alias]
                        (let [old (get-in current [:graph/aliases alias])]
                          (when (and old (not= old declaration-id))
                            (throw (ex-info "Graph alias conflict"
                                            {:error/category :graph/alias-conflict
                                             :alias alias :existing old
                                             :candidate declaration-id})))
                          (assoc-in current [:graph/aliases alias] declaration-id)))
                      graph (:rainbow/aliases declaration))
        graph (reduce #(put-edge %1 declaration-id :depends-on %2)
                      graph (:rainbow/dependencies declaration))]
    (if-not (contains? #{:theorem :axiom} (:rainbow/kind declaration))
      graph
      (let [claim-id (claim-id declaration)
            graph (put-node graph {:graph.node/id claim-id
                                   :graph.node/kind :claim
                                   :graph.node/claim (claim-content declaration)})
            graph (put-edge graph declaration-id :states claim-id)]
        (if (= :axiom (:rainbow/kind declaration))
          (put-edge graph declaration-id :asserts claim-id)
          (let [proof-id (proof-id declaration)
                graph (put-node graph {:graph.node/id proof-id
                                       :graph.node/kind :proof
                                       :graph.node/proof (proof-content declaration)})
                graph (-> graph
                          (put-edge proof-id :proves claim-id)
                          (put-edge proof-id :derived-from declaration-id))]
            (reduce #(put-edge %1 proof-id :depends-on %2)
                    graph (:rainbow/dependencies declaration))))))))

(defn add-environment [graph checked-environment]
  (reduce (fn [current id]
            (add-declaration current (environment/declaration checked-environment id)))
          graph
          (:rainbow.environment/order checked-environment)))

(defn add-foreign-objects
  "Adds a batch of raw foreign objects and their dependency edges without
  translating or registering native declarations. Dependencies outside the
  batch become explicit foreign-reference nodes."
  [graph objects]
  (let [duplicate-names (->> objects (map :foreign/name) frequencies
                             (keep (fn [[name count]] (when (> count 1) name)))
                             (sort-by str) vec)]
    (when (seq duplicate-names)
      (throw (ex-info "Foreign object names must be unique within a batch"
                      {:error/category :graph/duplicate-foreign-name
                       :foreign/names duplicate-names})))
    (doseq [object objects]
      (when-not (and (= :foreign-declaration (:rainbow/kind object))
                     (= 1 (:foreign/schema-version object))
                     (:foreign/system object)
                     (string? (:foreign/version object))
                     (string? (:foreign/commit object))
                     (string? (:foreign/name object))
                     (keyword? (:foreign/kind object))
                     (vector? (:foreign/dependencies object)))
        (throw (ex-info "Malformed raw foreign object"
                        {:error/category :graph/invalid-foreign-object
                         :foreign/object object}))))
    (let [ids-by-name (into {} (map (juxt :foreign/name foreign-object-id)) objects)
          with-objects
          (reduce (fn [current object]
                    (let [id (foreign-object-id object)]
                      (put-node current
                                {:graph.node/id id
                                 :graph.node/kind :foreign-declaration
                                 :graph.node/foreign-object object})))
                  graph objects)]
      (reduce
       (fn [current object]
         (let [from (foreign-object-id object)]
           (reduce
            (fn [current dependency]
              (let [to (or (get ids-by-name dependency)
                           (foreign-reference-id
                            (:foreign/system object) (:foreign/version object)
                            (:foreign/commit object) dependency))
                    current
                    (if (get ids-by-name dependency)
                      current
                      (put-node
                       current
                       {:graph.node/id to
                        :graph.node/kind :foreign-reference
                        :graph.node/foreign-reference
                        (foreign-reference-content
                         (:foreign/system object) (:foreign/version object)
                         (:foreign/commit object) dependency)}))]
                (put-edge current from :depends-on to)))
            current (:foreign/dependencies object))))
       with-objects objects))))

(defn- add-attempt [graph run-id attempt]
  (let [attempt-id (:attempt/id attempt)
        goal-id (:goal/hash attempt)
        graph (put-node graph {:graph.node/id goal-id
                               :graph.node/kind :goal-reference})
        graph (put-node graph {:graph.node/id attempt-id
                               :graph.node/kind :attempt
                               :graph.node/attempt attempt})]
    (-> graph
        (put-edge run-id :contains attempt-id)
        (put-edge attempt-id
                  (if (= :failure (:result attempt)) :failed-on :attempted)
                  goal-id))))

(defn add-run [graph run]
  (let [run-id (:run/id run)
        graph (put-node graph {:graph.node/id run-id
                               :graph.node/kind :run
                               :graph.node/run run})]
    (reduce #(add-attempt %1 run-id %2) graph (:attempts run))))

(defn add-runs [graph runs]
  (reduce add-run graph runs))

(defn dependencies [graph id]
  (into #{} (keep (fn [[from relation to]]
                    (when (and (= from id) (= relation :depends-on)) to)))
        (:graph/edges graph)))

(defn dependents [graph id]
  (into #{} (keep (fn [[from relation to]]
                    (when (and (= to id) (= relation :depends-on)) from)))
        (:graph/edges graph)))

(defn attempts-for [graph goal-id]
  (into []
        (keep (fn [[from relation to]]
                (when (and (= to goal-id) (contains? #{:failed-on :attempted} relation))
                  (get-in graph [:graph/nodes from :graph.node/attempt]))))
        (:graph/edges graph)))

(defn failed-goals [graph]
  (into #{} (keep (fn [[_ relation to]] (when (= :failed-on relation) to)))
        (:graph/edges graph)))

(defn resolve-alias [graph alias]
  (get-in graph [:graph/aliases alias]))

(defn graph-id [graph]
  (canonical/content-id
   {:graph/schema-version schema-version
    :nodes (into (sorted-map)
                 (map (fn [[id node]] [id (node-semantic-content node)]))
                 (:graph/nodes graph))
    :edges (vec (sort-by canonical/encode (:graph/edges graph)))}))

(defn validate [graph]
  (try
    (when-not (and (= :proof-graph (:rainbow/kind graph))
                   (= schema-version (:graph/schema-version graph)))
      (throw (ex-info "Unsupported graph schema"
                      {:error/category :graph/schema})))
    (doseq [[id node] (:graph/nodes graph)]
      (when-not (= id (:graph.node/id node))
        (throw (ex-info "Graph node map key differs from node ID"
                        {:error/category :graph/node-key-mismatch :key id})))
      (when-not (= id (expected-node-id node))
        (throw (ex-info "Graph node failed content validation"
                        {:error/category :graph/node-id-mismatch :id id}))))
    (doseq [[from _relation to :as edge] (:graph/edges graph)]
      (when-not (and (contains? (:graph/nodes graph) from)
                     (contains? (:graph/nodes graph) to))
        (throw (ex-info "Graph edge has a missing endpoint"
                        {:error/category :graph/missing-endpoint :edge edge}))))
    {:status :valid :graph graph :graph/id (graph-id graph)}
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected :error (ex-data exception) :message (ex-message exception)})))

(defn artifact [graph]
  {:rainbow.graph/schema-version schema-version
   :rainbow.graph/id (graph-id graph)
   :rainbow.graph/value graph})

(defn save! [graph path]
  (let [validation (validate graph)]
    (if-not (= :valid (:status validation))
      validation
      (do
        (spit path (str (pr-str (artifact graph)) "\n"))
        {:status :saved :path (str path) :graph/id (:graph/id validation)}))))

(defn replay-artifact [value]
  (if-not (= schema-version (:rainbow.graph/schema-version value))
    {:status :rejected :error {:error/category :graph/artifact-schema}}
    (let [validation (validate (:rainbow.graph/value value))]
      (if-not (= :valid (:status validation))
        validation
        (if (= (:rainbow.graph/id value) (:graph/id validation))
          {:status :replayed
           :graph (:rainbow.graph/value value)
           :graph/id (:graph/id validation)}
          {:status :rejected
           :error {:error/category :graph/artifact-id-mismatch
                   :expected (:rainbow.graph/id value)
                   :actual (:graph/id validation)}})))))

(defn load! [path]
  (try
    (replay-artifact (edn/read-string (slurp path)))
    (catch Exception exception
      {:status :rejected
       :error {:error/category :graph/malformed-artifact
               :class (str (class exception))}
       :message (.getMessage exception)})))
