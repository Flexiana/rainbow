(ns rainbow.history.mathlib-hidden-batch-4
  "Fourth proof-hidden Mathlib stroke: composition equivalences by reuse."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.history.mathlib-hidden-batch-2 :as mathlib-hidden-batch-2]
            [rainbow.history.mathlib-hidden-batch-3 :as mathlib-hidden-batch-3]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def report-path "artifacts/day29/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day29-statements.edn")
(def source-path "Mathlib/Logic/Function/Basic.lean")

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])

(def arrow function/arrow)
(def forall function/forall)
(def lam function/lam)
(def app function/app)
(def const* function/const*)
(def eq function/equality)

(defn composition [outer inner]
  (lam [['value 'C]] (app outer (app inner 'value))))

(defn congruent
  [domain-level codomain-level domain codomain callable left right evidence]
  (app (const* 'equality/congruent-function [domain-level codomain-level])
       domain codomain callable left right evidence))

(defn transitive [level carrier left middle right first-evidence second-evidence]
  (app (const* 'equality/transitive [level])
       carrier left middle right first-evidence second-evidence))

(defn conjunction-left [left right evidence]
  (app (const* 'proposition/left []) left right evidence))

(defn conjunction-right [left right evidence]
  (app (const* 'proposition/right []) left right evidence))

(defn conjoin [left right left-evidence right-evidence]
  (app (const* 'proposition/conjoin [])
       left right left-evidence right-evidence))

(defn witness [level carrier predicate value evidence]
  (app (const* 'proposition/witness [level])
       carrier predicate value evidence))

(defn use-witness [level carrier predicate result evidence continue]
  (app (const* 'proposition/use-witness [level])
       carrier predicate result evidence continue))

(def support-specs
  [{:name 'function/injective-composition
    :foreign/names []
    :universes ['u 'v 'w]
    :type
    (let [composed (composition 'f 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['left-injective (function/injective U V 'A 'B 'f)]
               ['right-injective (function/injective W U 'C 'A 'g)]]
              (function/injective W V 'C 'B composed)))
    :value
    (let [composed (composition 'f 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['left-injective (function/injective U V 'A 'B 'f)]
            ['right-injective (function/injective W U 'C 'A 'g)]
            ['x 'C] ['y 'C]
            ['same-image (eq V 'B (app composed 'x) (app composed 'y))]]
           (app 'right-injective 'x 'y
                (app 'left-injective (app 'g 'x) (app 'g 'y)
                     'same-image))))}

   {:name 'function/injective-of-composition
    :foreign/names []
    :universes ['u 'v 'w]
    :type
    (let [composed (composition 'f 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['composition-injective
                (function/injective W V 'C 'B composed)]]
              (function/injective W U 'C 'A 'g)))
    :value
    (let [composed (composition 'f 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['composition-injective
             (function/injective W V 'C 'B composed)]
            ['x 'C] ['y 'C]
            ['same-image (eq U 'A (app 'g 'x) (app 'g 'y))]]
           (app 'composition-injective 'x 'y
                (congruent U V 'A 'B 'f
                           (app 'g 'x) (app 'g 'y) 'same-image))))}

   {:name 'function/surjective-composition
    :foreign/names []
    :universes ['u 'v 'w]
    :type
    (let [composed (composition 'f 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['left-surjective (function/surjective U V 'A 'B 'f)]
               ['right-surjective (function/surjective W U 'C 'A 'g)]]
              (function/surjective W V 'C 'B composed)))
    :value
    (let [left-predicate
          (lam [['middle 'A]] (eq V 'B (app 'f 'middle) 'target))
          right-predicate
          (lam [['source 'C]] (eq U 'A (app 'g 'source) 'middle))
          result-predicate
          (lam [['source 'C]]
               (eq V 'B (app 'f (app 'g 'source)) 'target))]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['left-surjective (function/surjective U V 'A 'B 'f)]
            ['right-surjective (function/surjective W U 'C 'A 'g)]
            ['target 'B]]
           (use-witness
            U 'A left-predicate
            (proposition/existence W 'C result-predicate)
            (app 'left-surjective 'target)
            (lam [['middle 'A]
                  ['left-evidence (app left-predicate 'middle)]]
                 (use-witness
                  W 'C right-predicate
                  (proposition/existence W 'C result-predicate)
                  (app 'right-surjective 'middle)
                  (lam [['source 'C]
                        ['right-evidence (app right-predicate 'source)]]
                       (witness
                        W 'C result-predicate 'source
                        (transitive
                         V 'B (app 'f (app 'g 'source))
                         (app 'f 'middle) 'target
                         (congruent U V 'A 'B 'f
                                    (app 'g 'source) 'middle
                                    'right-evidence)
                         'left-evidence))))))))}

   {:name 'function/bijective-composition
    :foreign/names []
    :universes ['u 'v 'w]
    :type
    (let [composed (composition 'f 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['left-bijective (function/bijective U V 'A 'B 'f)]
               ['right-bijective (function/bijective W U 'C 'A 'g)]]
              (function/bijective W V 'C 'B composed)))
    :value
    (let [left-injective (function/injective U V 'A 'B 'f)
          left-surjective (function/surjective U V 'A 'B 'f)
          right-injective (function/injective W U 'C 'A 'g)
          right-surjective (function/surjective W U 'C 'A 'g)
          composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['left-bijective (function/bijective U V 'A 'B 'f)]
            ['right-bijective (function/bijective W U 'C 'A 'g)]]
           (conjoin
            composed-injective composed-surjective
            (app (const* 'function/injective-composition [U V W])
                 'A 'B 'C 'f 'g
                 (conjunction-left left-injective left-surjective
                                   'left-bijective)
                 (conjunction-left right-injective right-surjective
                                   'right-bijective))
            (app (const* 'function/surjective-composition [U V W])
                 'A 'B 'C 'f 'g
                 (conjunction-right left-injective left-surjective
                                    'left-bijective)
                 (conjunction-right right-injective right-surjective
                                    'right-bijective)))))}])

(def theorem-specs
  [{:name 'function/injective-composition-equivalence
    :foreign/names ["Function.Injective.of_comp_iff"]
    :universes ['u 'v 'w]
    :type
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          right-injective (function/injective W U 'C 'A 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)]
               ['left-injective (function/injective U V 'A 'B 'f)]
               ['g (arrow 'C 'A)]]
              (proposition/equivalence composed-injective right-injective)))
    :value
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          right-injective (function/injective W U 'C 'A 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)]
            ['left-injective (function/injective U V 'A 'B 'f)]
            ['g (arrow 'C 'A)]]
           (conjoin
            (arrow composed-injective right-injective)
            (arrow right-injective composed-injective)
            (lam [['composition-injective composed-injective]]
                 (app (const* 'function/injective-of-composition [U V W])
                      'A 'B 'C 'f 'g 'composition-injective))
            (lam [['right-injective right-injective]]
                 (app (const* 'function/injective-composition [U V W])
                      'A 'B 'C 'f 'g
                      'left-injective 'right-injective)))))}

   {:name 'function/injective-composition-equivalence-right-bijective
    :foreign/names ["Function.Injective.of_comp_iff'"]
    :universes ['u 'v 'w]
    :type
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          left-injective (function/injective U V 'A 'B 'f)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['right-bijective (function/bijective W U 'C 'A 'g)]]
              (proposition/equivalence composed-injective left-injective)))
    :value
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          left-injective (function/injective U V 'A 'B 'f)
          right-injective (function/injective W U 'C 'A 'g)
          right-surjective (function/surjective W U 'C 'A 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['right-bijective (function/bijective W U 'C 'A 'g)]]
           (conjoin
            (arrow composed-injective left-injective)
            (arrow left-injective composed-injective)
            (lam [['composition-injective composed-injective]]
                 (app (const*
                       'function/injective-of-composition-with-surjective-right
                       [U V W])
                      'A 'B 'C 'f 'g 'composition-injective
                      (conjunction-right right-injective right-surjective
                                         'right-bijective)))
            (lam [['left-injective left-injective]]
                 (app (const* 'function/injective-composition [U V W])
                      'A 'B 'C 'f 'g 'left-injective
                      (conjunction-left right-injective right-surjective
                                        'right-bijective))))))}

   {:name 'function/surjective-composition-equivalence
    :foreign/names ["Function.Surjective.of_comp_iff"]
    :universes ['u 'v 'w]
    :type
    (let [composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          left-surjective (function/surjective U V 'A 'B 'f)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['right-surjective (function/surjective W U 'C 'A 'g)]]
              (proposition/equivalence composed-surjective left-surjective)))
    :value
    (let [composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          left-surjective (function/surjective U V 'A 'B 'f)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['right-surjective (function/surjective W U 'C 'A 'g)]]
           (conjoin
            (arrow composed-surjective left-surjective)
            (arrow left-surjective composed-surjective)
            (lam [['composition-surjective composed-surjective]]
                 (app (const* 'function/surjective-of-composition [U V W])
                      'A 'B 'C 'f 'g 'composition-surjective))
            (lam [['left-surjective left-surjective]]
                 (app (const* 'function/surjective-composition [U V W])
                      'A 'B 'C 'f 'g
                      'left-surjective 'right-surjective)))))}

   {:name 'function/surjective-composition-equivalence-left-bijective
    :foreign/names ["Function.Surjective.of_comp_iff'"]
    :universes ['u 'v 'w]
    :type
    (let [composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          right-surjective (function/surjective W U 'C 'A 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)]
               ['left-bijective (function/bijective U V 'A 'B 'f)]
               ['g (arrow 'C 'A)]]
              (proposition/equivalence composed-surjective right-surjective)))
    :value
    (let [composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          right-surjective (function/surjective W U 'C 'A 'g)
          left-injective (function/injective U V 'A 'B 'f)
          left-surjective (function/surjective U V 'A 'B 'f)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)]
            ['left-bijective (function/bijective U V 'A 'B 'f)]
            ['g (arrow 'C 'A)]]
           (conjoin
            (arrow composed-surjective right-surjective)
            (arrow right-surjective composed-surjective)
            (lam [['composition-surjective composed-surjective]]
                 (app (const*
                       'function/surjective-of-composition-with-injective-left
                       [U V W])
                      'A 'B 'C 'f 'g 'composition-surjective
                      (conjunction-left left-injective left-surjective
                                        'left-bijective)))
            (lam [['right-surjective right-surjective]]
                 (app (const* 'function/surjective-composition [U V W])
                      'A 'B 'C 'f 'g
                      (conjunction-right left-injective left-surjective
                                         'left-bijective)
                      'right-surjective)))))}

   {:name 'function/bijective-composition-equivalence-right
    :foreign/names ["Function.Bijective.of_comp_iff"]
    :universes ['u 'v 'w]
    :type
    (let [composed-bijective
          (function/bijective W V 'C 'B (composition 'f 'g))
          left-bijective (function/bijective U V 'A 'B 'f)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
               ['right-bijective (function/bijective W U 'C 'A 'g)]]
              (proposition/equivalence composed-bijective left-bijective)))
    :value
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          composed-bijective
          (function/bijective W V 'C 'B (composition 'f 'g))
          left-injective (function/injective U V 'A 'B 'f)
          left-surjective (function/surjective U V 'A 'B 'f)
          left-bijective (function/bijective U V 'A 'B 'f)
          right-injective (function/injective W U 'C 'A 'g)
          right-surjective (function/surjective W U 'C 'A 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['right-bijective (function/bijective W U 'C 'A 'g)]]
           (conjoin
            (arrow composed-bijective left-bijective)
            (arrow left-bijective composed-bijective)
            (lam [['composition-bijective composed-bijective]]
                 (conjoin
                  left-injective left-surjective
                  (app (const*
                        'function/injective-of-composition-with-surjective-right
                        [U V W])
                       'A 'B 'C 'f 'g
                       (conjunction-left composed-injective composed-surjective
                                         'composition-bijective)
                       (conjunction-right right-injective right-surjective
                                          'right-bijective))
                  (app (const* 'function/surjective-of-composition [U V W])
                       'A 'B 'C 'f 'g
                       (conjunction-right composed-injective composed-surjective
                                          'composition-bijective))))
            (lam [['left-bijective left-bijective]]
                 (app (const* 'function/bijective-composition [U V W])
                      'A 'B 'C 'f 'g
                      'left-bijective 'right-bijective)))))}

   {:name 'function/bijective-composition-equivalence-left
    :foreign/names ["Function.Bijective.of_comp_iff'"]
    :universes ['u 'v 'w]
    :type
    (let [composed-bijective
          (function/bijective W V 'C 'B (composition 'f 'g))
          right-bijective (function/bijective W U 'C 'A 'g)]
      (forall [['A sort-u] ['B sort-v] ['C sort-w]
               ['f (arrow 'A 'B)]
               ['left-bijective (function/bijective U V 'A 'B 'f)]
               ['g (arrow 'C 'A)]]
              (proposition/equivalence composed-bijective right-bijective)))
    :value
    (let [composed-injective
          (function/injective W V 'C 'B (composition 'f 'g))
          composed-surjective
          (function/surjective W V 'C 'B (composition 'f 'g))
          composed-bijective
          (function/bijective W V 'C 'B (composition 'f 'g))
          left-injective (function/injective U V 'A 'B 'f)
          left-surjective (function/surjective U V 'A 'B 'f)
          right-injective (function/injective W U 'C 'A 'g)
          right-surjective (function/surjective W U 'C 'A 'g)
          right-bijective (function/bijective W U 'C 'A 'g)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)]
            ['left-bijective (function/bijective U V 'A 'B 'f)]
            ['g (arrow 'C 'A)]]
           (conjoin
            (arrow composed-bijective right-bijective)
            (arrow right-bijective composed-bijective)
            (lam [['composition-bijective composed-bijective]]
                 (conjoin
                  right-injective right-surjective
                  (app (const* 'function/injective-of-composition [U V W])
                       'A 'B 'C 'f 'g
                       (conjunction-left composed-injective composed-surjective
                                         'composition-bijective))
                  (app (const*
                        'function/surjective-of-composition-with-injective-left
                        [U V W])
                       'A 'B 'C 'f 'g
                       (conjunction-right composed-injective composed-surjective
                                          'composition-bijective)
                       (conjunction-left left-injective left-surjective
                                         'left-bijective))))
            (lam [['right-bijective right-bijective]]
                 (app (const* 'function/bijective-composition [U V W])
                      'A 'B 'C 'f 'g
                      'left-bijective 'right-bijective)))))}])

(def deferred-statements
  [{:foreign/name "Function.Injective.of_comp_iff._simp_1"
    :reason :requires-propositional-extensionality}
   {:foreign/name "Function.Injective.of_comp_iff'._simp_1"
    :reason :requires-propositional-extensionality}
   {:foreign/name "Function.Surjective.of_comp_iff._simp_1"
    :reason :requires-propositional-extensionality}
   {:foreign/name "Function.Surjective.of_comp_iff'._simp_1"
    :reason :requires-propositional-extensionality}])

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
  (let [prior (mathlib-hidden-batch-3/build)]
    (reduce
     (fn [{:keys [environment results] :as state} spec]
       (let [type (elaborate! environment (:type spec))
             value (elaborate! environment (:value spec))
             added
             (kernel/add-declaration
              environment
              {:rainbow/kind :theorem
               :rainbow/aliases #{(:name spec)}
               :rainbow/universes (:universes spec)
               :rainbow/type type :rainbow/value value
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
         (assoc state :environment (:environment added)
                :results (conj results
                               {:spec spec :declaration (:declaration added)}))))
     {:environment (:environment prior)
      :day27-results (:prior-results prior)
      :day28-results (:results prior)
      :results []}
     (concat support-specs theorem-specs))))

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
        {:keys [environment day27-results day28-results results]} (build)
        mappings (result-mappings results)
        earlier-mappings
        (vec (concat (get-in (mathlib-hidden-batch-1/report) [:proofs :mappings])
                     (mathlib-hidden-batch-2/result-mappings day27-results)
                     (mathlib-hidden-batch-3/result-mappings day28-results)))
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
             (= 6 (count mappings))
             (= 10 (count results) (count (distinct native-ids)))
             (= 32 (count proved-names) (:proved summary))
             (every? empty? (vals axioms))
             (true? (:proofs-redacted? summary)))
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
          :deferred
          (mapv #(assoc % :statement-weakened? false :trusted-axiom-added? false)
                deferred-statements)
          :lean-proofs-visible-to-rainbow? false
          :nativeization :composition-equivalences-from-checked-proof-data
          :statement-weakened? false}
         :proofs
         {:foreign-statements-checked (count mappings)
          :supporting-native-declarations (count support-specs)
          :mapped-native-declarations (count theorem-specs)
          :all-new-native-declarations (count results)
          :mappings mappings :axioms axioms}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings all-mappings}
         :measured-bottleneck
         {:category :propositional-extensionality
          :deferred-foreign-theorems (mapv :foreign/name deferred-statements)
          :action :deferred-without-axiom-or-weakened-statement}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib-day29/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day29/report-read-failed
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
