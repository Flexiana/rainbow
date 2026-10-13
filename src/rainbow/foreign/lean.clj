(ns rainbow.foreign.lean
  "Pinned Lean neutral-format importer for Rainbow's initial expression fragment."
  (:require [clojure.edn :as edn]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.graph :as graph]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.term :as term]))

(def pinned-version "4.30.0")
(def pinned-commit "d024af099ca4bf2c86f649261ebf59565dc8c622")

(def native-constant-aliases
  {"Nat" 'data/Nat
   "Nat.zero" 'data/zero
   "Nat.succ" 'data/succ})

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn load-neutral [path]
  (edn/read-string (slurp path)))

(defn- fixture-header-error [fixture]
  (cond
    (not= 1 (:foreign/schema-version fixture))
    [:foreign/schema-version "Unsupported Lean neutral schema"
     {:actual (:foreign/schema-version fixture)}]

    (not (and (= :lean (:foreign/system fixture))
              (= pinned-version (:foreign/version fixture))
              (= pinned-commit (:foreign/commit fixture))))
    [:foreign/toolchain-mismatch "Lean fixture does not match the pinned toolchain"
     {:expected {:version pinned-version :commit pinned-commit}
      :actual (select-keys fixture [:foreign/version :foreign/commit])}]))

(defn- raw-constant-names [form]
  (letfn [(walk [value]
            (cond
              (and (vector? value) (= :const (first value))
                   (string? (second value)))
              (into #{(second value)} (mapcat walk (drop 2 value)))

              (coll? value) (into #{} (mapcat walk value))
              :else #{}))]
    (walk form)))

(defn raw-foreign-object
  "Retains one Lean exporter declaration as graph data. No expression
  translation, host evaluation, or native declaration generation occurs."
  [fixture declaration]
  (let [dependencies (-> (into (raw-constant-names (:foreign/type declaration))
                                (raw-constant-names (:foreign/value declaration)))
                         sort vec)]
    (cond->
     {:rainbow/kind :foreign-declaration
      :foreign/schema-version 1
      :foreign/system (:foreign/system fixture)
      :foreign/version (:foreign/version fixture)
      :foreign/commit (:foreign/commit fixture)
      :foreign/name (:foreign/name declaration)
      :foreign/kind (:foreign/kind declaration)
      :foreign/universes (vec (:foreign/universes declaration))
      :foreign/raw-type (:foreign/type declaration)
      :foreign/raw-value (:foreign/value declaration)
      :foreign/unsafe? (true? (:foreign/unsafe? declaration))
      :foreign/partial? (true? (:foreign/partial? declaration))
      :foreign/dependencies dependencies}
      (:foreign/attributes declaration)
      (assoc :foreign/attributes (:foreign/attributes declaration))
      (:foreign/source declaration)
      (assoc :foreign/source (:foreign/source declaration))
      (:foreign/error declaration)
      (assoc :foreign/error (:foreign/error declaration)))))

(defn ingest-foreign-graph
  "Bulk-indexes a pinned neutral Lean fixture as raw foreign graph data. This
  deliberately tolerates expression constructors the native importer cannot
  translate and never changes a Rainbow kernel environment."
  ([fixture] (ingest-foreign-graph (graph/empty-graph) fixture))
  ([base-graph fixture]
   (try
     (when-let [[category message data] (fixture-header-error fixture)]
       (reject! category message data))
     (let [objects (mapv #(raw-foreign-object fixture %)
                         (:foreign/declarations fixture))
           value (graph/add-foreign-objects base-graph objects)
           validation (graph/validate value)]
       (if (= :valid (:status validation))
         {:status :ingested
          :fixture/id (canonical/content-id fixture)
          :graph value
          :graph/id (:graph/id validation)
          :objects objects
          :object-count (count objects)}
         validation))
     (catch clojure.lang.ExceptionInfo exception
       {:status :rejected
        :error (ex-data exception)
        :message (ex-message exception)}))))

(defn- translate-level [level universe-names path]
  (case (first level)
    :zero [:zero]
    :param (let [name (symbol (second level))]
             (if (contains? universe-names name)
               [:param name]
               (reject! :foreign/unbound-universe
                        "Lean level parameter is absent from the declaration"
                        {:path path :level level})))
    :succ [:succ (translate-level (second level) universe-names (conj path 1))]
    :max [:max (translate-level (second level) universe-names (conj path 1))
          (translate-level (nth level 2) universe-names (conj path 2))]
    :imax [:imax (translate-level (second level) universe-names (conj path 1))
           (translate-level (nth level 2) universe-names (conj path 2))]
    (reject! :foreign/unsupported-level "Unsupported Lean universe level"
             {:path path :level level})))

(defn- resolve-constant [environment imported name]
  (or (get imported name)
      (when-let [alias (get native-constant-aliases name)]
        (environment/resolve-id environment alias))))

(declare translate-expression)

(defn- translate-expression
  [environment imported expression universe-names path]
  (when-not (vector? expression)
    (reject! :foreign/malformed-expression "Lean expression must be tagged data"
             {:path path :expression expression}))
  (case (first expression)
    :sort [:sort (translate-level (second expression) universe-names (conj path 1))]
    :bound (let [index (second expression)]
             (if (and (integer? index) (not (neg? index)))
               [:bound index]
               (reject! :foreign/malformed-bound "Lean bound index must be natural"
                        {:path (conj path 1) :index index})))
    :const (let [name (second expression)
                 id (resolve-constant environment imported name)]
             (when-not id
               (reject! :foreign/unknown-constant "Lean constant has no native/imported mapping"
                        {:path (conj path 1) :foreign/name name}))
             [:const id
              (mapv (fn [index level]
                      (translate-level level universe-names (conj path 2 index)))
                    (range) (nth expression 2))])
    :app [:app (translate-expression environment imported (second expression)
                                     universe-names (conj path 1))
          (translate-expression environment imported (nth expression 2)
                                universe-names (conj path 2))]
    (:lam :pi)
    (let [mode (nth expression 3)]
      (when-not (contains? #{:explicit :implicit} mode)
        (reject! :foreign/unsupported-binder
                 "Initial bridge supports explicit and ordinary implicit binders"
                 {:path (conj path 3) :binder mode}))
      [(first expression)
       (translate-expression environment imported (second expression)
                             universe-names (conj path 1))
       (translate-expression environment imported (nth expression 2)
                             universe-names (conj path 2))
       mode])
    :let [:let (translate-expression environment imported (second expression)
                                      universe-names (conj path 1))
          (translate-expression environment imported (nth expression 2)
                                universe-names (conj path 2))
          (translate-expression environment imported (nth expression 3)
                                universe-names (conj path 3))]
    (reject! :foreign/unsupported-expression "Unsupported Lean expression constructor"
             {:path path :expression expression :constructor (first expression)})))

(defn foreign-alias [name]
  (symbol "foreign.lean" (string/replace name "/" "$")))

(defn- import-declaration [environment imported fixture declaration]
  (let [name (:foreign/name declaration)
        kind (:foreign/kind declaration)
        universes (mapv symbol (:foreign/universes declaration))
        universe-names (set universes)
        base-path [:foreign/declarations name]
        _ (when (:foreign/error declaration)
            (reject! :foreign/export-error "Lean exporter reported a declaration error"
                     {:path base-path :declaration declaration}))
        _ (when (:foreign/unsafe? declaration)
            (reject! :foreign/unsafe-declaration "Unsafe Lean declarations are not importable"
                     {:path (conj base-path :foreign/unsafe?) :foreign/name name}))
        _ (when-not (contains? #{:definition :theorem :axiom} kind)
            (reject! :foreign/unsupported-declaration-kind
                     "Lean declaration kind is outside the initial bridge"
                     {:path (conj base-path :foreign/kind) :kind kind}))
        type (translate-expression environment imported (:foreign/type declaration)
                                   universe-names (conj base-path :foreign/type))
        value (when-some [raw (:foreign/value declaration)]
                (translate-expression environment imported raw universe-names
                                      (conj base-path :foreign/value)))
        candidate
        {:rainbow/kind kind
         :rainbow/aliases #{(foreign-alias name)}
         :rainbow/universes universes
         :rainbow/type type
         :rainbow/value value
         :rainbow/transparency (if (= :definition kind) :reducible :opaque)
         :rainbow/dependencies (into (term/constants type)
                                     (if value (term/constants value) #{}))
         :rainbow/provenance {:origin :foreign
                              :foreign/system :lean
                              :foreign/version (:foreign/version fixture)
                              :foreign/commit (:foreign/commit fixture)
                              :foreign/name name
                              :foreign/unsafe? false}
         :rainbow/schema-version 1}
        result (kernel/add-declaration environment candidate)]
    (when-not (= :accepted (:status result))
      (reject! :foreign/kernel-rejected "Translated Lean declaration failed Rainbow recheck"
               {:path base-path :foreign/name name :cause result
                :translated/type type :translated/value value}))
    (let [checked (:declaration result)
          object {:rainbow/kind :foreign-declaration
                  :foreign/system :lean
                  :foreign/version (:foreign/version fixture)
                  :foreign/commit (:foreign/commit fixture)
                  :foreign/name name
                  :foreign/kind kind
                  :foreign/raw-type (:foreign/type declaration)
                  :foreign/raw-value (:foreign/value declaration)
                  :foreign/translated-type type
                  :foreign/translated-value value
                  :foreign/native-declaration-id (:rainbow/id checked)
                  :foreign/check {:status :accepted}
                  :foreign/provenance {:unsafe? false :axiom? (= :axiom kind)}}]
      {:environment (:environment result)
       :name name
       :id (:rainbow/id checked)
       :object object})))

(defn import-fixture [environment fixture]
  (try
    (when-let [[category message data] (fixture-header-error fixture)]
      (reject! category message data))
    (let [result
          (reduce (fn [{:keys [environment imported objects]} declaration]
                    (let [imported-result
                          (import-declaration environment imported fixture declaration)]
                      {:environment (:environment imported-result)
                       :imported (assoc imported (:name imported-result) (:id imported-result))
                       :objects (conj objects (:object imported-result))}))
                  {:environment environment :imported {} :objects []}
                  (:foreign/declarations fixture))]
      (assoc result
             :status :imported
             :fixture/id (canonical/content-id fixture)
             :native-mappings native-constant-aliases))
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(defn base-environment []
  (let [result (persistence/load-environment "artifacts/day9/environment.edn")]
    (when-not (= :replayed (:status result))
      (throw (ex-info "Day-9 environment failed replay" {:result result})))
    (:environment result)))

(defn build []
  (import-fixture (base-environment)
                  (load-neutral "artifacts/day12/lean-neutral.edn")))

(defn report []
  (let [{:keys [status environment objects fixture/id] :as result} (build)]
    (if-not (= :imported status)
      result
      {:status :passed
       :toolchain {:version pinned-version :commit pinned-commit}
       :fixture/id id
       :imports (count objects)
       :kinds (frequencies (map :foreign/kind objects))
       :axioms (into {} (map (fn [object]
                              [(:foreign/name object)
                               (kernel/axioms environment
                                              (:foreign/native-declaration-id object))])
                            objects))
       :foreign-objects (mapv #(select-keys % [:foreign/name
                                               :foreign/native-declaration-id
                                               :foreign/check])
                              objects)
       :declarations (count (:rainbow.environment/declarations environment))})))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (:environment (build)) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
