(ns rainbow.history.mathlib-surjective-lifting
  "Generated proof-hidden Mathlib stroke for surjective quantifier lifting."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.history.mathlib-hidden-batch-2 :as mathlib-hidden-batch-2]
            [rainbow.history.mathlib-hidden-batch-3 :as mathlib-hidden-batch-3]
            [rainbow.history.mathlib-hidden-batch-4 :as mathlib-hidden-batch-4]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.quantifier :as quantifier]
            [rainbow.term :as term]))

(def report-path "artifacts/day30/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day30-statements.edn")
(def source-path "Mathlib/Logic/Function/Basic.lean")

(def U [:param 'u])
(def V [:param 'v])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def arrow function/arrow)
(def forall function/forall)
(def lam function/lam)
(def app function/app)
(def const* function/const*)
(def eq function/equality)

(def foreign-names
  {:forall {1 "Function.Surjective.forall"
            2 "Function.Surjective.forall₂"
            3 "Function.Surjective.forall₃"}
   :exists {1 "Function.Surjective.exists"
            2 "Function.Surjective.exists₂"
            3 "Function.Surjective.exists₃"}})

(defn variables [prefix arity]
  (mapv #(symbol (str prefix %)) (range 1 (inc arity))))

(defn predicate-type [arity]
  (apply arrow (concat (repeat arity 'B) ['Prop])))

(defn predicate-application [predicate arguments]
  (apply app predicate arguments))

(defn mapped-arguments [source-names]
  (mapv #(app 'f %) source-names))

(defn substitution [from to evidence motive proof]
  (app (const* 'equality/substitution [V])
       'B from to evidence motive proof))

(defn reverse-substitution [from to evidence motive proof]
  (app (const* 'equality/reverse-substitution [V])
       'B from to evidence motive proof))

(defn transport-mapped-to-target
  [target-names source-names evidence-names proof]
  (reduce
   (fn [current index]
     (let [arguments
           (vec (concat (take index target-names)
                        ['replacement]
                        (drop (inc index) (mapped-arguments source-names))))
           source (app 'f (nth source-names index))
           target (nth target-names index)]
       (substitution source target (nth evidence-names index)
                     (lam [['replacement 'B]]
                          (predicate-application 'P arguments))
                     current)))
   proof (range (count target-names))))

(defn transport-target-to-mapped
  [target-names source-names evidence-names proof]
  (reduce
   (fn [current index]
     (let [arguments
           (vec (concat (take index (mapped-arguments source-names))
                        ['replacement]
                        (drop (inc index) target-names)))
           source (app 'f (nth source-names index))
           target (nth target-names index)]
       (reverse-substitution
        source target (nth evidence-names index)
        (lam [['replacement 'B]]
             (predicate-application 'P arguments))
        current)))
   proof (range (count target-names))))

(defn choose-preimages
  [target-names source-names evidence-names result continuation]
  (letfn [(step [index]
            (if (= index (count target-names))
              (continuation)
              (let [target (nth target-names index)
                    source (nth source-names index)
                    evidence (nth evidence-names index)
                    predicate
                    (lam [['candidate 'A]]
                         (eq V 'B (app 'f 'candidate) target))]
                (app (const* 'proposition/use-witness [U])
                     'A predicate result (app 'surjective target)
                     (lam [[source 'A] [evidence (app predicate source)]]
                          (step (inc index)))))))]
    (step 0)))

(defn forall-spec [arity]
  (let [targets (variables "target-" arity)
        sources (variables "source-" arity)
        evidences (variables "preimage-" arity)
        target-bindings (mapv #(vector % 'B) targets)
        source-bindings (mapv #(vector % 'A) sources)
        target-body (predicate-application 'P targets)
        source-body (predicate-application 'P (mapped-arguments sources))
        target-forall (quantifier/nested-forall target-bindings target-body)
        source-forall (quantifier/nested-forall source-bindings source-body)]
    {:name (symbol "function" (str "surjective-forall-" arity))
     :foreign/names [(get-in foreign-names [:forall arity])]
     :universes ['u 'v]
     :type
     (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
              ['surjective (function/surjective U V 'A 'B 'f)]
              ['P (predicate-type arity)]]
             (proposition/equivalence target-forall source-forall))
     :value
     (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
           ['surjective (function/surjective U V 'A 'B 'f)]
           ['P (predicate-type arity)]]
          (app
           (const* 'proposition/conjoin [])
           (arrow target-forall source-forall)
           (arrow source-forall target-forall)
           (lam [['all-targets target-forall]]
                (lam source-bindings
                     (apply app 'all-targets (mapped-arguments sources))))
           (lam [['all-sources source-forall]]
                (lam target-bindings
                     (choose-preimages
                      targets sources evidences target-body
                      #(transport-mapped-to-target
                        targets sources evidences
                        (apply app 'all-sources sources)))))))}))

(defn exists-spec [arity]
  (let [targets (variables "target-" arity)
        sources (variables "source-" arity)
        evidences (variables "preimage-" arity)
        target-bindings (mapv #(vector % 'B) targets)
        source-bindings (mapv #(vector % 'A) sources)
        target-body (predicate-application 'P targets)
        source-body (predicate-application 'P (mapped-arguments sources))
        target-exists (quantifier/nested-existence V target-bindings target-body)
        source-exists (quantifier/nested-existence U source-bindings source-body)]
    {:name (symbol "function" (str "surjective-exists-" arity))
     :foreign/names [(get-in foreign-names [:exists arity])]
     :universes ['u 'v]
     :type
     (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
              ['surjective (function/surjective U V 'A 'B 'f)]
              ['P (predicate-type arity)]]
             (proposition/equivalence target-exists source-exists))
     :value
     (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
           ['surjective (function/surjective U V 'A 'B 'f)]
           ['P (predicate-type arity)]]
          (app
           (const* 'proposition/conjoin [])
           (arrow target-exists source-exists)
           (arrow source-exists target-exists)
           (lam [['target-evidence target-exists]]
                (quantifier/eliminate-existences
                 V target-bindings target-body 'target-evidence source-exists
                 (fn [predicate-evidence]
                   (choose-preimages
                    targets sources evidences source-exists
                    #(quantifier/introduce-existences
                      U source-bindings sources source-body
                      (transport-target-to-mapped
                       targets sources evidences predicate-evidence))))))
           (lam [['source-evidence source-exists]]
                (quantifier/eliminate-existences
                 U source-bindings source-body 'source-evidence target-exists
                 (fn [predicate-evidence]
                   (quantifier/introduce-existences
                    V target-bindings (mapped-arguments sources)
                    target-body predicate-evidence))))))}))

(def theorem-specs
  (vec (concat (map forall-spec (range 1 4))
               (map exists-spec (range 1 4)))))

(def requested-foreign-names (set (mapcat :foreign/names theorem-specs)))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Generated quantifier form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (let [prior (mathlib-hidden-batch-4/build)]
    (reduce
     (fn [{:keys [environment results] :as state} spec]
       (let [type (elaborate! environment (:type spec))
             value (elaborate! environment (:value spec))
             added
             (kernel/add-declaration
              environment
              {:rainbow/kind :theorem :rainbow/aliases #{(:name spec)}
               :rainbow/universes (:universes spec)
               :rainbow/type type :rainbow/value value
               :rainbow/transparency :opaque
               :rainbow/dependencies
               (into (term/constants type) (term/constants value))
               :rainbow/provenance
               {:origin :native :producer :generated-quantifier-reproof
                :foreign/system :lean :foreign/library :mathlib
                :foreign/version mathlib/pinned-version
                :foreign/commit mathlib/pinned-commit
                :foreign/source source-path
                :foreign/names (:foreign/names spec)
                :foreign/proof-hidden? true :generator/arity
                (Long/parseLong (str (last (str (:name spec)))))}
               :rainbow/schema-version 1})]
         (when-not (= :accepted (:status added))
           (throw (ex-info "Generated quantifier proof rejected"
                           {:spec (:name spec) :result added})))
         (assoc state :environment (:environment added)
                :results (conj results
                               {:spec spec :declaration (:declaration added)}))))
     {:environment (:environment prior) :prior prior :results []}
     theorem-specs)))

(defn result-mappings [results]
  (mapv (fn [result]
          {:foreign/name (first (get-in result [:spec :foreign/names]))
           :native/id (get-in result [:declaration :rainbow/id])})
        results))

(defn all-mappings
  "Flattens the accumulated Mathlib proof lineage through Day 30.

  Later strokes call this instead of depending on the nested shape of every
  preceding build result."
  [{:keys [prior results]}]
  (vec (concat (get-in (mathlib-hidden-batch-1/report) [:proofs :mappings])
               (mathlib-hidden-batch-2/result-mappings (:day27-results prior))
               (mathlib-hidden-batch-3/result-mappings (:day28-results prior))
               (mathlib-hidden-batch-4/result-mappings (:results prior))
               (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        {:keys [environment prior results]} (build)
        mappings (result-mappings results)
        all-mappings (all-mappings {:prior prior :results results})
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        axioms (into {}
                     (map (fn [result]
                            [(get-in result [:spec :name])
                             (kernel/axioms environment
                                            (get-in result [:declaration
                                                            :rainbow/id]))]))
                     results)
        native-ids (mapv #(get-in % [:declaration :rainbow/id]) results)
        batch-names (set (map :foreign/name (:statements batch)))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names batch-names)
             (= 6 (count mappings) (count results)
                (count (distinct native-ids)))
             (= 38 (count proved-names) (:proved summary))
             (every? empty? (vals axioms)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :path source-path}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested (count batch-names)
          :proof-values :redacted}
         :selection
         {:foreign-theorems (vec (sort batch-names))
          :independently-proved (count mappings)
          :lean-proofs-visible-to-rainbow? false
          :nativeization :generated-nested-quantifier-proof-data
          :statement-weakened? false}
         :proofs {:foreign-statements-checked (count mappings)
                  :generated-arities [1 2 3]
                  :mappings mappings :axioms axioms}
         :coverage {:independently-proved (:proved summary)
                    :theorem-declarations (:theorems summary)
                    :ratio (get-in summary [:coverage :ratio])
                    :percent (* 100 (get-in summary [:coverage :ratio]))
                    :all-mappings all-mappings}
         :capability-growth
         {:generator 'rainbow.math.quantifier
          :families [:forall :exists]
          :arity-range [1 3]
          :generated-terms-kernel-checked? true}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib-day30/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day30/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command second-path]]
  (if (= "replay" command)
    (let [result (load-report (or second-path report-path))]
      (println (pr-str result))
      (when-not (= :replayed (:status result)) (System/exit 1)))
    (let [value (report (or command default-catalog-path)
                        (or second-path default-statement-path))]
      (println (pr-str value))
      (when-not (= :passed (:status value)) (System/exit 1)))))
