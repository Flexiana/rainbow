(ns rainbow.history.mathlib-hidden-batch-2
  "Second proof-hidden Mathlib stroke: native function proof data and reuse."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def report-path "artifacts/day27/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day27-statements.edn")
(def source-path "Mathlib/Logic/Function/Basic.lean")
(def source-url
  (str "https://github.com/leanprover-community/mathlib4/blob/"
       mathlib/pinned-commit "/" source-path))

(def U [:param 'u])
(def V [:param 'v])
(def sort-u [:sort U])
(def sort-v [:sort V])

(defn arrow [& values] (into [:->] values))
(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn app [function & arguments] (into [:app function] arguments))
(defn const* [alias levels] [:const alias (vec levels)])

(defn eq [level carrier left right]
  (app (const* 'equality/Eq [level]) carrier left right))

(defn involutive [level carrier function]
  (rainbow.math.logic.function/involutive level carrier function))

(def injective function/injective)

(def surjective function/surjective)

(def bijective function/bijective)

(defn symmetric [level carrier left right evidence]
  (app (const* 'equality/symmetric [level])
       carrier left right evidence))

(defn transitive [level carrier left middle right first-evidence second-evidence]
  (app (const* 'equality/transitive [level])
       carrier left middle right first-evidence second-evidence))

(defn congruent
  [domain-level codomain-level domain codomain function left right evidence]
  (app (const* 'equality/congruent-function [domain-level codomain-level])
       domain codomain function left right evidence))

(def theorem-specs
  [{:name 'function/involutive-self-inverse
    :foreign/names ["Function.Involutive.leftInverse"
                    "Function.Involutive.rightInverse"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]
             ['h (involutive U 'A 'f)] ['x 'A]]
            (eq U 'A (app 'f (app 'f 'x)) 'x))
    :value
    (lam [['A sort-u] ['f (arrow 'A 'A)]
          ['h (involutive U 'A 'f)] ['x 'A]]
         (app 'h 'x))}

   {:name 'function/involutive-injective
    :foreign/names ["Function.Involutive.injective"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]
             ['h (involutive U 'A 'f)]]
            (injective U U 'A 'A 'f))
    :value
    (lam [['A sort-u] ['f (arrow 'A 'A)]
          ['h (involutive U 'A 'f)]
          ['x 'A] ['y 'A]
          ['same-image (eq U 'A (app 'f 'x) (app 'f 'y))]]
         (transitive
          U 'A 'x (app 'f (app 'f 'x)) 'y
          (symmetric U 'A (app 'f (app 'f 'x)) 'x (app 'h 'x))
          (transitive
           U 'A (app 'f (app 'f 'x)) (app 'f (app 'f 'y)) 'y
           (congruent U U 'A 'A 'f
                      (app 'f 'x) (app 'f 'y) 'same-image)
           (app 'h 'y))))}

   {:name 'function/involutive-surjective
    :foreign/names ["Function.Involutive.surjective"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]
             ['h (involutive U 'A 'f)]]
            (surjective U U 'A 'A 'f))
    :value
    (let [predicate
          (lam [['source 'A]]
               (eq U 'A (app 'f 'source) 'target))]
      (lam [['A sort-u] ['f (arrow 'A 'A)]
            ['h (involutive U 'A 'f)] ['target 'A]]
           (app (const* 'proposition/witness [U])
                'A predicate (app 'f 'target) (app 'h 'target))))}

   {:name 'function/involutive-bijective
    :foreign/names ["Function.Involutive.bijective"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]
             ['h (involutive U 'A 'f)]]
            (bijective U U 'A 'A 'f))
    :value
    (let [injective-type (injective U U 'A 'A 'f)
          surjective-type (surjective U U 'A 'A 'f)]
      (lam [['A sort-u] ['f (arrow 'A 'A)]
            ['h (involutive U 'A 'f)]]
           (app (const* 'proposition/conjoin [])
                injective-type surjective-type
                (app (const* 'function/involutive-injective [U]) 'A 'f 'h)
                (app (const* 'function/involutive-surjective [U]) 'A 'f 'h))))}

   {:name 'function/bijective-injective
    :foreign/names ["Function.Bijective.injective"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
             ['h (bijective U V 'A 'B 'f)]]
            (injective U V 'A 'B 'f))
    :value
    (let [injective-type (injective U V 'A 'B 'f)
          surjective-type (surjective U V 'A 'B 'f)]
      (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
            ['h (bijective U V 'A 'B 'f)]]
           (app (const* 'proposition/left [])
                injective-type surjective-type 'h)))}

   {:name 'function/bijective-surjective
    :foreign/names ["Function.Bijective.surjective"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
             ['h (bijective U V 'A 'B 'f)]]
            (surjective U V 'A 'B 'f))
    :value
    (let [injective-type (injective U V 'A 'B 'f)
          surjective-type (surjective U V 'A 'B 'f)]
      (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
            ['h (bijective U V 'A 'B 'f)]]
           (app (const* 'proposition/right [])
                injective-type surjective-type 'h)))}

   {:name 'function/left-inverse-surjective
    :foreign/names ["Function.LeftInverse.surjective"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v]
             ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
             ['h (forall [['target 'B]]
                         (eq V 'B (app 'f (app 'g 'target)) 'target))]]
            (surjective U V 'A 'B 'f))
    :value
    (let [predicate
          (lam [['source 'A]]
               (eq V 'B (app 'f 'source) 'target))]
      (lam [['A sort-u] ['B sort-v]
            ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
            ['h (forall [['target 'B]]
                        (eq V 'B (app 'f (app 'g 'target)) 'target))]
            ['target 'B]]
           (app (const* 'proposition/witness [U])
                'A predicate (app 'g 'target) (app 'h 'target))))}

   {:name 'function/right-inverse-injective
    :foreign/names ["Function.RightInverse.injective"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v]
             ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
             ['h (forall [['source 'A]]
                         (eq U 'A (app 'g (app 'f 'source)) 'source))]]
            (injective U V 'A 'B 'f))
    :value
    (lam [['A sort-u] ['B sort-v]
          ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
          ['h (forall [['source 'A]]
                      (eq U 'A (app 'g (app 'f 'source)) 'source))]
          ['x 'A] ['y 'A]
          ['same-image (eq V 'B (app 'f 'x) (app 'f 'y))]]
         (transitive
          U 'A 'x (app 'g (app 'f 'x)) 'y
          (symmetric U 'A (app 'g (app 'f 'x)) 'x (app 'h 'x))
          (transitive
           U 'A (app 'g (app 'f 'x)) (app 'g (app 'f 'y)) 'y
           (congruent V U 'B 'A 'g
                      (app 'f 'x) (app 'f 'y) 'same-image)
           (app 'h 'y))))}])

(def deferred-statements
  [{:foreign/name "Function.Involutive.comp_self"
    :reason :requires-function-extensionality
    :statement-weakened? false
    :trusted-axiom-added? false}])

(def requested-foreign-names
  (set (concat (mapcat :foreign/names theorem-specs)
               (map :foreign/name deferred-statements))))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Mathlib-derived form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (reduce
   (fn [{:keys [environment results]} spec]
     (let [type (elaborate! environment (:type spec))
           value (elaborate! environment (:value spec))
           added
           (kernel/add-declaration
            environment
            {:rainbow/kind :theorem
             :rainbow/aliases #{(:name spec)}
             :rainbow/universes (:universes spec)
             :rainbow/type type
             :rainbow/value value
             :rainbow/transparency :opaque
             :rainbow/dependencies
             (into (term/constants type) (term/constants value))
             :rainbow/provenance
             {:origin :native :producer :independent-mathlib-reproof
              :foreign/system :lean :foreign/library :mathlib
              :foreign/version mathlib/pinned-version
              :foreign/commit mathlib/pinned-commit
              :foreign/source source-path
              :foreign/names (:foreign/names spec)
              :foreign/proof-hidden? true}
             :rainbow/schema-version 1})]
       (when-not (= :accepted (:status added))
         (throw (ex-info "Mathlib-derived proof rejected"
                         {:spec (:name spec) :result added})))
       {:environment (:environment added)
        :results (conj results {:spec spec :declaration (:declaration added)})}))
   {:environment (proposition/build-environment) :results []}
   theorem-specs))

(defn result-mappings [results]
  (mapv (fn [[foreign-name native-id]]
          {:foreign/name foreign-name :native/id native-id})
        (sort-by first
                 (mapcat
                  (fn [result]
                    (let [native-id (get-in result [:declaration :rainbow/id])]
                      (map (fn [foreign-name] [foreign-name native-id])
                           (get-in result [:spec :foreign/names]))))
                  results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        {:keys [environment results]} (build)
        mappings (result-mappings results)
        earlier-mappings (get-in (mathlib-hidden-batch-1/report) [:proofs :mappings])
        all-mappings (vec (concat earlier-mappings mappings))
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        axioms (into {}
                     (map (fn [result]
                            [(get-in result [:spec :name])
                             (kernel/axioms
                              environment
                              (get-in result [:declaration :rainbow/id]))]))
                     results)
        native-ids (mapv #(get-in % [:declaration :rainbow/id]) results)
        batch-names (set (map :foreign/name (:statements batch)))
        passed?
        (and (= :verified (:status batch))
             (= requested-foreign-names batch-names)
             (= 10 (count batch-names))
             (= 9 (count mappings))
             (= 8 (count results) (count (distinct native-ids)))
             (= 14 (count proved-names) (:proved summary))
             (every? empty? (vals axioms))
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :path source-path :url source-url}
         :statement-batch
         {:status (:status batch)
          :id (:batch/id batch)
          :catalog/id (:catalog/id batch)
          :requested (count requested-foreign-names)
          :proof-values :redacted}
         :selection
         {:foreign-theorems (vec (sort batch-names))
          :independently-proved (count mappings)
          :deferred deferred-statements
          :lean-proofs-visible-to-rainbow? false
          :nativeization
          :expanded-function-predicates-with-native-proof-data-connectives
          :statement-weakened? false}
         :proofs
         {:foreign-statements-checked (count mappings)
          :native-declarations (count results)
          :distinct-native-declarations (count (distinct native-ids))
          :foreign-theorem-reuse
          [{:native/id (:native/id (first (filter
                                           #(= "Function.Involutive.leftInverse"
                                               (:foreign/name %))
                                           mappings)))
            :foreign/names ["Function.Involutive.leftInverse"
                            "Function.Involutive.rightInverse"]}]
          :mappings mappings
          :axioms axioms}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings all-mappings}
         :measured-bottleneck
         {:category :function-extensionality
          :foreign/name "Function.Involutive.comp_self"
          :action :deferred-without-axiom-or-weakened-statement}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib-day27/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day27/report-read-failed
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
