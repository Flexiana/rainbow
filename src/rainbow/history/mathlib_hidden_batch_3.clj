(ns rainbow.history.mathlib-hidden-batch-3
  "Third proof-hidden Mathlib stroke: constructive composition and expansion."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.history.mathlib-hidden-batch-2 :as mathlib-hidden-batch-2]
            [rainbow.elaborate :as elaborate]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def report-path "artifacts/day28/report.edn")
(def default-catalog-path "/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz")
(def default-statement-path "/tmp/rainbow-day28-proving.edn")
(def source-path "Mathlib/Logic/Function/Basic.lean")
(def source-url
  (str "https://github.com/leanprover-community/mathlib4/blob/"
       mathlib/pinned-commit "/" source-path))

(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def sort-u [:sort U])
(def sort-v [:sort V])
(def sort-w [:sort W])
(def proposition-level [:succ [:zero]])

(defn arrow [& values] (into [:->] values))
(defn forall [bindings body] [:forall (vec bindings) body])
(defn lam [bindings body] [:fn (vec bindings) body])
(defn app [callable & arguments] (into [:app callable] arguments))
(defn const* [alias levels] [:const alias (vec levels)])
(def eq function/equality)

(defn composed [outer inner value]
  (app outer (app inner value)))

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

(defn witness [level carrier predicate value evidence]
  (app (const* 'proposition/witness [level])
       carrier predicate value evidence))

(defn use-witness [level carrier predicate result evidence continue]
  (app (const* 'proposition/use-witness [level])
       carrier predicate result evidence continue))

(def theorem-specs
  [{:name 'function/inverse-direction
    :foreign/names ["Function.LeftInverse.rightInverse"
                    "Function.RightInverse.leftInverse"]
    :universes ['u 'v]
    :type
    (let [inverse
          (forall [['x 'A]]
                  (eq U 'A (app 'g (app 'f 'x)) 'x))]
      (forall [['A sort-u] ['B sort-v]
               ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
               ['h inverse]]
              inverse))
    :value
    (let [inverse
          (forall [['x 'A]]
                  (eq U 'A (app 'g (app 'f 'x)) 'x))]
      (lam [['A sort-u] ['B sort-v]
            ['f (arrow 'A 'B)] ['g (arrow 'B 'A)]
            ['h inverse]]
           'h))}

   {:name 'function/surjective-of-composition
    :foreign/names ["Function.Surjective.of_comp"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
             ['h (function/surjective
                  W V 'C 'B (lam [['source 'C]]
                                 (composed 'f 'g 'source)))]]
            (function/surjective U V 'A 'B 'f))
    :value
    (let [composed-predicate
          (lam [['source 'C]]
               (eq V 'B (composed 'f 'g 'source) 'target))
          result-predicate
          (lam [['source 'A]]
               (eq V 'B (app 'f 'source) 'target))]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['h (function/surjective
                 W V 'C 'B (lam [['source 'C]]
                                (composed 'f 'g 'source)))]
            ['target 'B]]
           (use-witness
            W 'C composed-predicate
            (proposition/existence U 'A result-predicate)
            (app 'h 'target)
            (lam [['source 'C] ['evidence (app composed-predicate 'source)]]
                 (witness U 'A result-predicate (app 'g 'source) 'evidence)))))}

   {:name 'function/injective-of-composition-with-surjective-right
    :foreign/names ["Function.Injective.of_comp_right"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
             ['composition-injective
              (function/injective
               W V 'C 'B (lam [['source 'C]]
                              (composed 'f 'g 'source)))]
             ['right-surjective (function/surjective W U 'C 'A 'g)]]
            (function/injective U V 'A 'B 'f))
    :value
    (let [left-preimage
          (lam [['source 'C]] (eq U 'A (app 'g 'source) 'x))
          right-preimage
          (lam [['source 'C]] (eq U 'A (app 'g 'source) 'y))
          result (eq U 'A 'x 'y)]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['composition-injective
             (function/injective
              W V 'C 'B (lam [['source 'C]]
                             (composed 'f 'g 'source)))]
            ['right-surjective (function/surjective W U 'C 'A 'g)]
            ['x 'A] ['y 'A]
            ['same-image (eq V 'B (app 'f 'x) (app 'f 'y))]]
           (use-witness
            W 'C left-preimage result (app 'right-surjective 'x)
            (lam [['left-source 'C]
                  ['left-evidence (app left-preimage 'left-source)]]
                 (use-witness
                  W 'C right-preimage result (app 'right-surjective 'y)
                  (lam [['right-source 'C]
                        ['right-evidence (app right-preimage 'right-source)]]
                       (let [left-image (app 'f (app 'g 'left-source))
                             right-image (app 'f (app 'g 'right-source))
                             source-equality
                             (app 'composition-injective
                                  'left-source 'right-source
                                  (transitive
                                   V 'B left-image (app 'f 'x) right-image
                                   (congruent U V 'A 'B 'f
                                              (app 'g 'left-source) 'x
                                              'left-evidence)
                                   (transitive
                                    V 'B (app 'f 'x) (app 'f 'y) right-image
                                    'same-image
                                    (symmetric
                                     V 'B right-image (app 'f 'y)
                                     (congruent U V 'A 'B 'f
                                                (app 'g 'right-source) 'y
                                                'right-evidence)))))]
                         (transitive
                          U 'A 'x (app 'g 'left-source) 'y
                          (symmetric U 'A (app 'g 'left-source) 'x
                                     'left-evidence)
                          (transitive
                           U 'A (app 'g 'left-source)
                           (app 'g 'right-source) 'y
                           (congruent W U 'C 'A 'g
                                      'left-source 'right-source source-equality)
                           'right-evidence)))))))))}

   {:name 'function/surjective-of-composition-with-injective-left
    :foreign/names ["Function.Surjective.of_comp_left"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
             ['composition-surjective
              (function/surjective
               W V 'C 'B (lam [['source 'C]]
                              (composed 'f 'g 'source)))]
             ['left-injective (function/injective U V 'A 'B 'f)]]
            (function/surjective W U 'C 'A 'g))
    :value
    (let [composed-predicate
          (lam [['source 'C]]
               (eq V 'B (composed 'f 'g 'source) (app 'f 'target)))
          result-predicate
          (lam [['source 'C]]
               (eq U 'A (app 'g 'source) 'target))]
      (lam [['A sort-u] ['B sort-v] ['C sort-w]
            ['f (arrow 'A 'B)] ['g (arrow 'C 'A)]
            ['composition-surjective
             (function/surjective
              W V 'C 'B (lam [['source 'C]]
                             (composed 'f 'g 'source)))]
            ['left-injective (function/injective U V 'A 'B 'f)]
            ['target 'A]]
           (use-witness
            W 'C composed-predicate
            (proposition/existence W 'C result-predicate)
            (app 'composition-surjective (app 'f 'target))
            (lam [['source 'C] ['evidence (app composed-predicate 'source)]]
                 (witness W 'C result-predicate 'source
                          (app 'left-injective
                               (app 'g 'source) 'target 'evidence))))))}

   {:name 'function/injective2-left-section
    :foreign/names ["Function.Injective2.left"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B 'C)]
             ['h (function/injective2 U V W 'A 'B 'C 'f)]
             ['fixed 'B]]
            (function/injective
             U W 'A 'C (lam [['value 'A]] (app 'f 'value 'fixed))))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['f (arrow 'A 'B 'C)]
          ['h (function/injective2 U V W 'A 'B 'C 'f)]
          ['fixed 'B] ['x 'A] ['y 'A]
          ['same-image (eq W 'C (app 'f 'x 'fixed)
                            (app 'f 'y 'fixed))]]
         (let [left-equality (eq U 'A 'x 'y)
               right-equality (eq V 'B 'fixed 'fixed)]
           (app (const* 'proposition/left [])
                left-equality right-equality
                (app 'h 'x 'y 'fixed 'fixed 'same-image))))}

   {:name 'function/injective2-right-section
    :foreign/names ["Function.Injective2.right"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['f (arrow 'A 'B 'C)]
             ['h (function/injective2 U V W 'A 'B 'C 'f)]
             ['fixed 'A]]
            (function/injective
             V W 'B 'C (lam [['value 'B]] (app 'f 'fixed 'value))))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['f (arrow 'A 'B 'C)]
          ['h (function/injective2 U V W 'A 'B 'C 'f)]
          ['fixed 'A] ['x 'B] ['y 'B]
          ['same-image (eq W 'C (app 'f 'fixed 'x)
                            (app 'f 'fixed 'y))]]
         (let [left-equality (eq U 'A 'fixed 'fixed)
               right-equality (eq V 'B 'x 'y)]
           (app (const* 'proposition/right [])
                left-equality right-equality
                (app 'h 'fixed 'fixed 'x 'y 'same-image))))}

   {:name 'function/involutive-equality-equivalence
    :foreign/names ["Function.Involutive.eq_iff"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]
             ['h (function/involutive U 'A 'f)]
             ['x 'A] ['y 'A]]
            (proposition/equivalence
             (eq U 'A (app 'f 'x) 'y)
             (eq U 'A 'x (app 'f 'y))))
    :value
    (let [forward-type
          (arrow (eq U 'A (app 'f 'x) 'y)
                 (eq U 'A 'x (app 'f 'y)))
          backward-type
          (arrow (eq U 'A 'x (app 'f 'y))
                 (eq U 'A (app 'f 'x) 'y))]
      (lam [['A sort-u] ['f (arrow 'A 'A)]
            ['h (function/involutive U 'A 'f)]
            ['x 'A] ['y 'A]]
           (app (const* 'proposition/conjoin [])
                forward-type backward-type
                (lam [['evidence (eq U 'A (app 'f 'x) 'y)]]
                     (transitive
                      U 'A 'x (app 'f (app 'f 'x)) (app 'f 'y)
                      (symmetric U 'A (app 'f (app 'f 'x)) 'x
                                 (app 'h 'x))
                      (congruent U U 'A 'A 'f
                                 (app 'f 'x) 'y 'evidence)))
                (lam [['evidence (eq U 'A 'x (app 'f 'y))]]
                     (transitive
                      U 'A (app 'f 'x) (app 'f (app 'f 'y)) 'y
                      (congruent U U 'A 'A 'f
                                 'x (app 'f 'y) 'evidence)
                      (app 'h 'y))))))}

   {:name 'function/evaluate-apply
    :foreign/names ["Function.eval_apply"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u]
             ['family (forall [['value 'A]] sort-v)]
             ['x 'A]
             ['f (forall [['value 'A]] (app 'family 'value))]]
            (eq V (app 'family 'x) (app 'f 'x) (app 'f 'x)))
    :value
    (lam [['A sort-u]
          ['family (forall [['value 'A]] sort-v)]
          ['x 'A]
          ['f (forall [['value 'A]] (app 'family 'value))]]
         (app (const* 'equality/reflexive [V])
              (app 'family 'x) (app 'f 'x)))}

   {:name 'function/lift-binary-apply
    :foreign/names ["Function.onFun_apply"]
    :universes ['u 'v 'w]
    :type
    (forall [['A sort-u] ['B sort-v] ['C sort-w]
             ['combine (arrow 'B 'B 'C)]
             ['project (arrow 'A 'B)]
             ['x 'A] ['y 'A]]
            (eq W 'C
                (app 'combine (app 'project 'x) (app 'project 'y))
                (app 'combine (app 'project 'x) (app 'project 'y))))
    :value
    (lam [['A sort-u] ['B sort-v] ['C sort-w]
          ['combine (arrow 'B 'B 'C)]
          ['project (arrow 'A 'B)]
          ['x 'A] ['y 'A]]
         (app (const* 'equality/reflexive [W])
              'C (app 'combine (app 'project 'x) (app 'project 'y))))}

   {:name 'function/constant-definition
    :foreign/names ["Function.const_def"]
    :universes ['u 'v]
    :type
    (forall [['A sort-u] ['B sort-v] ['value 'B]]
            (eq [:imax U V] (arrow 'A 'B)
                (lam [['ignored 'A]] 'value)
                (lam [['ignored 'A]] 'value)))
    :value
    (lam [['A sort-u] ['B sort-v] ['value 'B]]
         (app (const* 'equality/reflexive [[:imax U V]])
              (arrow 'A 'B) (lam [['ignored 'A]] 'value)))}

   {:name 'function/involutive-definition
    :foreign/names ["Function.Involutive.eq_1"]
    :universes ['u]
    :type
    (forall [['A sort-u] ['f (arrow 'A 'A)]]
            (eq proposition-level 'Prop
                (function/involutive U 'A 'f)
                (function/involutive U 'A 'f)))
    :value
    (lam [['A sort-u] ['f (arrow 'A 'A)]]
         (app (const* 'equality/reflexive [proposition-level])
              'Prop (function/involutive U 'A 'f)))}])

(def requested-foreign-names
  (set (mapcat :foreign/names theorem-specs)))

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Mathlib-derived form failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(defn build []
  (let [prior (mathlib-hidden-batch-2/build)]
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
         (assoc state
                :environment (:environment added)
                :results (conj results
                               {:spec spec :declaration (:declaration added)}))))
     {:environment (:environment prior) :prior-results (:results prior) :results []}
     theorem-specs)))

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
        {:keys [environment prior-results results]} (build)
        mappings (result-mappings results)
        earlier-mappings
        (vec (concat (get-in (mathlib-hidden-batch-1/report) [:proofs :mappings])
                     (mathlib-hidden-batch-2/result-mappings prior-results)))
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
             (= 12 (count batch-names) (count mappings))
             (= 11 (count results) (count (distinct native-ids)))
             (= 26 (count proved-names) (:proved summary))
             (every? empty? (vals axioms))
             (true? (:proofs-redacted? summary)))
        base
        {:status (if passed? :passed :failed)
         :source {:library :mathlib :version mathlib/pinned-version
                  :commit mathlib/pinned-commit :path source-path :url source-url}
         :statement-batch
         {:status (:status batch) :id (:batch/id batch)
          :catalog/id (:catalog/id batch)
          :requested (count requested-foreign-names)
          :proof-values :redacted}
         :selection
         {:foreign-theorems (vec (sort batch-names))
          :independently-proved (count mappings)
          :lean-proofs-visible-to-rainbow? false
          :nativeization
          :expanded-function-predicates-composition-and-definition-data
          :statement-weakened? false}
         :proofs
         {:foreign-statements-checked (count mappings)
          :native-declarations (count results)
          :distinct-native-declarations (count (distinct native-ids))
          :foreign-theorem-reuse
          [{:native/id
            (:native/id
             (first (filter #(= "Function.LeftInverse.rightInverse"
                                (:foreign/name %))
                            mappings)))
            :foreign/names ["Function.LeftInverse.rightInverse"
                            "Function.RightInverse.leftInverse"]}]
          :mappings mappings :axioms axioms}
         :coverage
         {:independently-proved (:proved summary)
          :theorem-declarations (:theorems summary)
          :ratio (get-in summary [:coverage :ratio])
          :percent (* 100 (get-in summary [:coverage :ratio]))
          :all-mappings all-mappings}
         :capability-growth
         {:reusable-function-predicate-namespace 'rainbow.math.logic.function
          :constructive-existential-elimination? true
          :multi-theorem-proof-reuse? true}
         :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :mathlib-day28/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :mathlib-day28/report-read-failed
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
