(ns rainbow.history.mathlib-unique-existence-transport
  "Proof-hidden Mathlib stroke for constructive unique-existence transport."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-surjective-lifting :as mathlib-surjective-lifting]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def report-path "artifacts/day31/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day31-statements.edn")
(def source-paths
  ["Mathlib/Logic/ExistsUnique.lean"
   "Mathlib/Logic/Function/Basic.lean"])

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

(defn reflexive [level carrier value]
  (app (const* 'equality/reflexive [level]) carrier value))

(defn symmetric [level carrier left right evidence]
  (app (const* 'equality/symmetric [level])
       carrier left right evidence))

(defn transitive [level carrier left middle right first-evidence second-evidence]
  (app (const* 'equality/transitive [level])
       carrier left middle right first-evidence second-evidence))

(defn congruent
  [domain-level codomain-level domain codomain callable left right evidence]
  (app (const* 'equality/congruent-function [domain-level codomain-level])
       domain codomain callable left right evidence))

(defn reverse-substitution [level carrier left right evidence predicate proof]
  (app (const* 'equality/reverse-substitution [level])
       carrier left right evidence predicate proof))

(defn conjoin [left right left-evidence right-evidence]
  (app (const* 'proposition/conjoin [])
       left right left-evidence right-evidence))

(defn conjunction-left [left right evidence]
  (app (const* 'proposition/left []) left right evidence))

(defn conjunction-right [left right evidence]
  (app (const* 'proposition/right []) left right evidence))

(defn witness [level carrier predicate value evidence]
  (app (const* 'proposition/witness [level])
       carrier predicate value evidence))

(defn use-witness [level carrier predicate result evidence continue]
  (app (const* 'proposition/use-witness [level])
       carrier predicate result evidence continue))

(defn unique-witness [level carrier predicate value evidence unique]
  (app (const* 'proposition/unique-witness [level])
       carrier predicate value evidence unique))

(defn use-unique-witness
  [level carrier predicate result evidence continue]
  (app (const* 'proposition/use-unique-witness [level])
       carrier predicate result evidence continue))

(defn pointwise-forward [left right iff-evidence value proof]
  (app (conjunction-left (arrow (app left value) (app right value))
                         (arrow (app right value) (app left value))
                         (app iff-evidence value))
       proof))

(defn pointwise-backward [left right iff-evidence value proof]
  (app (conjunction-right (arrow (app left value) (app right value))
                          (arrow (app right value) (app left value))
                          (app iff-evidence value))
       proof))

(defn injective-from [bijective]
  (conjunction-left
   (function/injective U V 'A 'B 'f)
   (function/surjective U V 'A 'B 'f)
   bijective))

(defn surjective-from [bijective]
  (conjunction-right
   (function/injective U V 'A 'B 'f)
   (function/surjective U V 'A 'B 'f)
   bijective))

(def theorem-specs
  [{:name 'proposition/unique-equality-right
    :foreign/names ["existsUnique_eq"]
    :source "Mathlib/Logic/ExistsUnique.lean"
    :universes ['u]
    :type
    (forall [['A sort-u] ['value 'A]]
            (proposition/unique-existence
             U 'A (lam [['candidate 'A]]
                       (eq U 'A 'candidate 'value))))
    :value
    (let [predicate (lam [['candidate 'A]]
                         (eq U 'A 'candidate 'value))]
      (lam [['A sort-u] ['value 'A]]
           (unique-witness
            U 'A predicate 'value
            (reflexive U 'A 'value)
            (lam [['candidate 'A]
                  ['candidate-evidence (app predicate 'candidate)]]
                 'candidate-evidence))))}

   {:name 'proposition/unique-equality-left
    :foreign/names ["existsUnique_eq'"]
    :source "Mathlib/Logic/ExistsUnique.lean"
    :universes ['u]
    :type
    (forall [['A sort-u] ['value 'A]]
            (proposition/unique-existence
             U 'A (lam [['candidate 'A]]
                       (eq U 'A 'value 'candidate))))
    :value
    (let [predicate (lam [['candidate 'A]]
                         (eq U 'A 'value 'candidate))]
      (lam [['A sort-u] ['value 'A]]
           (unique-witness
            U 'A predicate 'value
            (reflexive U 'A 'value)
            (lam [['candidate 'A]
                  ['candidate-evidence (app predicate 'candidate)]]
                 (symmetric U 'A 'value 'candidate
                            'candidate-evidence)))))}

   {:name 'proposition/unique-from-existence-and-global-uniqueness
    :foreign/names ["existsUnique_of_exists_of_unique"]
    :source "Mathlib/Logic/ExistsUnique.lean"
    :universes ['u]
    :type
    (forall [['A sort-u]
             ['predicate (arrow 'A 'Prop)]
             ['some-evidence (proposition/existence U 'A 'predicate)]
             ['globally-unique
              (forall [['left 'A] ['right 'A]
                       ['left-evidence (app 'predicate 'left)]
                       ['right-evidence (app 'predicate 'right)]]
                      (eq U 'A 'left 'right))]]
            (proposition/unique-existence U 'A 'predicate))
    :value
    (lam [['A sort-u]
          ['predicate (arrow 'A 'Prop)]
          ['some-evidence (proposition/existence U 'A 'predicate)]
          ['globally-unique
           (forall [['left 'A] ['right 'A]
                    ['left-evidence (app 'predicate 'left)]
                    ['right-evidence (app 'predicate 'right)]]
                   (eq U 'A 'left 'right))]]
         (use-witness
          U 'A 'predicate
          (proposition/unique-existence U 'A 'predicate)
          'some-evidence
          (lam [['value 'A] ['evidence (app 'predicate 'value)]]
               (unique-witness
                U 'A 'predicate 'value 'evidence
                (lam [['candidate 'A]
                      ['candidate-evidence (app 'predicate 'candidate)]]
                     (app 'globally-unique
                          'candidate 'value
                          'candidate-evidence 'evidence))))))}

   {:name 'proposition/unique-existence-congruence
    :foreign/names ["existsUnique_congr"]
    :source "Mathlib/Logic/ExistsUnique.lean"
    :universes ['u]
    :type
    (forall [['A sort-u]
             ['left (arrow 'A 'Prop)]
             ['right (arrow 'A 'Prop)]
             ['pointwise
              (forall [['value 'A]]
                      (proposition/equivalence
                       (app 'left 'value) (app 'right 'value)))]]
            (proposition/equivalence
             (proposition/unique-existence U 'A 'left)
             (proposition/unique-existence U 'A 'right)))
    :value
    (let [left-unique (proposition/unique-existence U 'A 'left)
          right-unique (proposition/unique-existence U 'A 'right)]
      (lam [['A sort-u]
            ['left (arrow 'A 'Prop)]
            ['right (arrow 'A 'Prop)]
            ['pointwise
             (forall [['value 'A]]
                     (proposition/equivalence
                      (app 'left 'value) (app 'right 'value)))]]
           (conjoin
            (arrow left-unique right-unique)
            (arrow right-unique left-unique)
            (lam [['left-evidence left-unique]]
                 (use-unique-witness
                  U 'A 'left right-unique 'left-evidence
                  (lam [['value 'A]
                        ['evidence (app 'left 'value)]
                        ['unique (proposition/uniqueness
                                  U 'A 'left 'value)]]
                       (unique-witness
                        U 'A 'right 'value
                        (pointwise-forward
                         'left 'right 'pointwise 'value 'evidence)
                        (lam [['candidate 'A]
                              ['candidate-evidence
                               (app 'right 'candidate)]]
                             (app
                              'unique 'candidate
                              (pointwise-backward
                               'left 'right 'pointwise
                               'candidate 'candidate-evidence)))))))
            (lam [['right-evidence right-unique]]
                 (use-unique-witness
                  U 'A 'right left-unique 'right-evidence
                  (lam [['value 'A]
                        ['evidence (app 'right 'value)]
                        ['unique (proposition/uniqueness
                                  U 'A 'right 'value)]]
                       (unique-witness
                        U 'A 'left 'value
                        (pointwise-backward
                         'left 'right 'pointwise 'value 'evidence)
                        (lam [['candidate 'A]
                              ['candidate-evidence
                               (app 'left 'candidate)]]
                             (app
                              'unique 'candidate
                              (pointwise-forward
                               'left 'right 'pointwise
                               'candidate 'candidate-evidence))))))))))}

   {:name 'function/bijective-unique-preimage
    :foreign/names ["Function.Bijective.existsUnique"]
    :source "Mathlib/Logic/Function/Basic.lean"
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
             ['bijective (function/bijective U V 'A 'B 'f)]
             ['target 'B]]
            (proposition/unique-existence
             U 'A (lam [['source 'A]]
                       (eq V 'B (app 'f 'source) 'target))))
    :value
    (let [predicate
          (lam [['source 'A]]
               (eq V 'B (app 'f 'source) 'target))]
      (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
            ['bijective (function/bijective U V 'A 'B 'f)]
            ['target 'B]]
           (use-witness
            U 'A predicate
            (proposition/unique-existence U 'A predicate)
            (app (surjective-from 'bijective) 'target)
            (lam [['source 'A]
                  ['source-evidence (app predicate 'source)]]
                 (unique-witness
                  U 'A predicate 'source 'source-evidence
                  (lam [['candidate 'A]
                        ['candidate-evidence (app predicate 'candidate)]]
                       (app
                        (injective-from 'bijective)
                        'candidate 'source
                        (transitive
                         V 'B (app 'f 'candidate) 'target
                         (app 'f 'source)
                         'candidate-evidence
                         (symmetric
                          V 'B (app 'f 'source) 'target
                          'source-evidence)))))))))}

   {:name 'function/bijective-equivalence-unique-preimages
    :foreign/names ["Function.bijective_iff_existsUnique"]
    :source "Mathlib/Logic/Function/Basic.lean"
    :universes ['u 'v]
    :type
    (let [all-unique
          (forall [['target 'B]]
                  (proposition/unique-existence
                   U 'A (lam [['source 'A]]
                             (eq V 'B (app 'f 'source) 'target))))]
      (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]]
              (proposition/equivalence
               (function/bijective U V 'A 'B 'f)
               all-unique)))
    :value
    (let [bijective (function/bijective U V 'A 'B 'f)
          predicate
          (lam [['source 'A]]
               (eq V 'B (app 'f 'source) 'target))
          all-unique
          (forall [['target 'B]]
                  (proposition/unique-existence U 'A predicate))
          injective (function/injective U V 'A 'B 'f)
          surjective (function/surjective U V 'A 'B 'f)]
      (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]]
           (conjoin
            (arrow bijective all-unique)
            (arrow all-unique bijective)
            (lam [['bijective-evidence bijective] ['target 'B]]
                 (app (const* 'function/bijective-unique-preimage [U V])
                      'A 'B 'f 'bijective-evidence 'target))
            (lam [['all-unique-evidence all-unique]]
                 (conjoin
                  injective surjective
                  (lam [['left 'A] ['right 'A]
                        ['same-image
                         (eq V 'B (app 'f 'left) (app 'f 'right))]]
                       (let [right-predicate
                             (lam [['source 'A]]
                                  (eq V 'B (app 'f 'source)
                                      (app 'f 'right)))]
                         (use-unique-witness
                          U 'A right-predicate
                          (eq U 'A 'left 'right)
                          (app 'all-unique-evidence (app 'f 'right))
                          (lam [['unique-value 'A]
                                ['unique-evidence
                                 (app right-predicate 'unique-value)]
                                ['unique
                                 (proposition/uniqueness
                                  U 'A right-predicate 'unique-value)]]
                               (transitive
                                U 'A 'left 'unique-value 'right
                                (app 'unique 'left 'same-image)
                                (symmetric
                                 U 'A 'right 'unique-value
                                 (app 'unique 'right
                                      (reflexive
                                       V 'B (app 'f 'right)))))))))
                  (lam [['target 'B]]
                       (use-unique-witness
                        U 'A predicate
                        (proposition/existence U 'A predicate)
                        (app 'all-unique-evidence 'target)
                        (lam [['source 'A]
                              ['source-evidence (app predicate 'source)]
                              ['unique
                               (proposition/uniqueness
                                U 'A predicate 'source)]]
                             (witness U 'A predicate
                                      'source 'source-evidence)))))))))}

   {:name 'function/bijective-unique-existence-transport
    :foreign/names ["Function.Bijective.existsUnique_iff"]
    :source "Mathlib/Logic/Function/Basic.lean"
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
             ['bijective (function/bijective U V 'A 'B 'f)]
             ['predicate (arrow 'B 'Prop)]]
            (proposition/equivalence
             (proposition/unique-existence V 'B 'predicate)
             (proposition/unique-existence
              U 'A (lam [['source 'A]]
                        (app 'predicate (app 'f 'source))))))
    :value
    (let [source-predicate
          (lam [['source 'A]]
               (app 'predicate (app 'f 'source)))
          target-unique
          (proposition/unique-existence V 'B 'predicate)
          source-unique
          (proposition/unique-existence U 'A source-predicate)]
      (lam [['A sort-u] ['B sort-v] ['f (arrow 'A 'B)]
            ['bijective (function/bijective U V 'A 'B 'f)]
            ['predicate (arrow 'B 'Prop)]]
           (conjoin
            (arrow target-unique source-unique)
            (arrow source-unique target-unique)
            (lam [['target-evidence target-unique]]
                 (use-unique-witness
                  V 'B 'predicate source-unique 'target-evidence
                  (lam [['target 'B]
                        ['predicate-evidence (app 'predicate 'target)]
                        ['target-uniqueness
                         (proposition/uniqueness
                          V 'B 'predicate 'target)]]
                       (let [preimage-predicate
                             (lam [['source 'A]]
                                  (eq V 'B (app 'f 'source) 'target))]
                         (use-witness
                          U 'A preimage-predicate source-unique
                          (app (surjective-from 'bijective) 'target)
                          (lam [['source 'A]
                                ['preimage-evidence
                                 (app preimage-predicate 'source)]]
                               (unique-witness
                                U 'A source-predicate 'source
                                (reverse-substitution
                                 V 'B (app 'f 'source) 'target
                                 'preimage-evidence 'predicate
                                 'predicate-evidence)
                                (lam [['candidate 'A]
                                      ['candidate-evidence
                                       (app source-predicate 'candidate)]]
                                     (app
                                      (injective-from 'bijective)
                                      'candidate 'source
                                      (transitive
                                       V 'B (app 'f 'candidate) 'target
                                       (app 'f 'source)
                                       (app 'target-uniqueness
                                            (app 'f 'candidate)
                                            'candidate-evidence)
                                       (symmetric
                                        V 'B (app 'f 'source) 'target
                                        'preimage-evidence)))))))))))
            (lam [['source-evidence source-unique]]
                 (use-unique-witness
                  U 'A source-predicate target-unique 'source-evidence
                  (lam [['source 'A]
                        ['predicate-evidence
                         (app source-predicate 'source)]
                        ['source-uniqueness
                         (proposition/uniqueness
                          U 'A source-predicate 'source)]]
                       (unique-witness
                        V 'B 'predicate (app 'f 'source)
                        'predicate-evidence
                        (lam [['candidate-target 'B]
                              ['candidate-evidence
                               (app 'predicate 'candidate-target)]]
                             (let [preimage-predicate
                                   (lam [['candidate-source 'A]]
                                        (eq V 'B
                                            (app 'f 'candidate-source)
                                            'candidate-target))]
                               (use-witness
                                U 'A preimage-predicate
                                (eq V 'B 'candidate-target
                                    (app 'f 'source))
                                (app (surjective-from 'bijective)
                                     'candidate-target)
                                (lam [['candidate-source 'A]
                                      ['preimage-evidence
                                       (app preimage-predicate
                                            'candidate-source)]]
                                     (transitive
                                      V 'B 'candidate-target
                                      (app 'f 'candidate-source)
                                      (app 'f 'source)
                                      (symmetric
                                       V 'B (app 'f 'candidate-source)
                                       'candidate-target
                                       'preimage-evidence)
                                      (congruent
                                       U V 'A 'B 'f
                                       'candidate-source 'source
                                       (app
                                        'source-uniqueness
                                        'candidate-source
                                        (reverse-substitution
                                         V 'B
                                         (app 'f 'candidate-source)
                                         'candidate-target
                                         'preimage-evidence
                                         'predicate
                                         'candidate-evidence)))))))))))))))}])

(def deferred-statements
  [{:foreign/name "existsUnique_prop"
    :reason :requires-proof-irrelevance
    :statement-weakened? false
    :trusted-axiom-added? false}
   {:foreign/name "existsUnique_prop_of_true"
    :reason :requires-proof-irrelevance
    :statement-weakened? false
    :trusted-axiom-added? false}])

(def proved-foreign-names (set (mapcat :foreign/names theorem-specs)))
(def deferred-foreign-names (set (map :foreign/name deferred-statements)))
(def requested-foreign-names
  (into proved-foreign-names deferred-foreign-names))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Unique-existence form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (let [prior (mathlib-surjective-lifting/build)]
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
               :rainbow/type type
               :rainbow/value value
               :rainbow/transparency :opaque
               :rainbow/dependencies
               (into (term/constants type) (term/constants value))
               :rainbow/provenance
               {:origin :native :producer :unique-existence-proof-data
                :foreign/system :lean :foreign/library :mathlib
                :foreign/version mathlib/pinned-version
                :foreign/commit mathlib/pinned-commit
                :foreign/source (:source spec)
                :foreign/names (:foreign/names spec)
                :foreign/proof-hidden? true}
               :rainbow/schema-version 1})]
         (when-not (= :accepted (:status added))
           (throw (ex-info "Unique-existence proof rejected"
                           {:spec (:name spec) :result added})))
         (assoc state
                :environment (:environment added)
                :results (conj results
                               {:spec spec
                                :declaration (:declaration added)}))))
     {:environment (:environment prior) :prior prior :results []}
     theorem-specs)))

(defn result-mappings [results]
  (mapv (fn [result]
          {:foreign/name (first (get-in result [:spec :foreign/names]))
           :native/id (get-in result [:declaration :rainbow/id])})
        results))

(defn all-mappings
  "Flattens the accumulated Mathlib proof lineage through Day 31."
  [{:keys [prior results]}]
  (vec (concat (mathlib-surjective-lifting/all-mappings prior)
               (result-mappings results))))

(defn report [catalog-path statement-path]
  (let [batch (mathlib/verify-statement-batch
               catalog-path statement-path requested-foreign-names)
        {:keys [environment prior results]} (build)
        mappings (result-mappings results)
        all-mappings (all-mappings {:prior prior :results results})
        proved-names (set (map :foreign/name all-mappings))
        summary (mathlib/summarize catalog-path proved-names)
        axioms
        (into {}
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
             (= 9 (count batch-names))
             (= 7 (count mappings) (count results)
                (count (distinct native-ids)))
             (= 45 (count proved-names) (:proved summary))
             (= deferred-foreign-names
                (set (map :foreign/name deferred-statements)))
             (every? empty? (vals axioms))
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :paths source-paths}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch) :requested (count batch-names)
          :proof-values :redacted}
         :selection
         {:foreign-theorems (vec (sort batch-names))
          :independently-proved (count mappings)
          :deferred (count deferred-statements)
          :lean-proofs-visible-to-rainbow? false
          :nativeization :unique-existence-proof-data-and-transport
          :statement-weakened? false}
         :proofs {:foreign-statements-checked (count mappings)
                  :mappings mappings :axioms axioms}
         :deferred-statements deferred-statements
         :coverage {:independently-proved (:proved summary)
                    :theorem-declarations (:theorems summary)
                    :ratio (get-in summary [:coverage :ratio])
                    :percent (* 100 (get-in summary [:coverage :ratio]))
                    :all-mappings all-mappings}
         :capability-growth
         {:native-connective 'proposition/unique-existence
          :introduction 'proposition/unique-witness
          :elimination 'proposition/use-unique-witness
          :exporter-fix :compacted-region-owned-name-lifetime}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected
         :error/category :mathlib-day31/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day31/report-read-failed
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
