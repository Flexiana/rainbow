(ns rainbow.math.prelude-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib-native :as mathlib-native]
            [rainbow.kernel :as kernel]
            [rainbow.math.prelude :as prelude]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.term :as term]))

(deftest measured-prelude-concepts-and-data-extend-an-existing-environment
  (let [extended (prelude/extend-environment (proposition/build-environment))]
    (doseq [alias (vals prelude/constant-aliases)]
      (is (string? (environment/resolve-id extended alias))))
    (is (= 5 (count (:rainbow.environment/blocks extended))))))

(deftest measured-logical-combinators-extend-the-frozen-prelude
  (let [base (prelude/extend-environment (proposition/build-environment))
        extended (prelude/extend-combinators base)]
    (doseq [alias (vals prelude/combinator-constant-aliases)]
      (is (string? (environment/resolve-id extended alias))))))

(deftest dependent-subtype-projections-iota-reduce-as-proof-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes)
        level [:succ [:zero]]
        bool (proposition/const* 'data/Bool [])
        predicate (proposition/lam [['ignored bool]] (proposition/truth))
        true-value (proposition/const* 'data/true [])
        evidence (proposition/const* 'proposition/trivial [])
        source (proposition/app
                (proposition/const* 'data/subtype [level])
                bool predicate true-value evidence)
        value-expression
        (proposition/app (proposition/const* 'subtype/value [level])
                         bool predicate source)
        property-expression
        (proposition/app (proposition/const* 'subtype/property [level])
                         bool predicate source)
        core #(-> (elaborate/core-expression checked %) :term)
        normalized-value (kernel/normalize checked (core value-expression))
        normalized-property (kernel/normalize checked (core property-expression))]
    (doseq [alias (vals prelude/subtype-constant-aliases)]
      (is (string? (environment/resolve-id checked alias))))
    (is (= (core true-value) (:term normalized-value)))
    (is (= (core evidence) (:term normalized-property)))
    (is (= :checked
           (:status (kernel/infer checked (core property-expression)))))))

(deftest inductive-membership-dictionaries-compute-through-recursor-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes
                    prelude/extend-inductive-memberships)
        zero [:zero]
        data-level [:succ zero]
        bool (proposition/const* 'data/Bool [])
        value (proposition/const* 'data/false [])
        list-empty (proposition/app (proposition/const* 'data/nil [data-level])
                                    bool)
        option-empty
        (proposition/app (proposition/const* 'data/none [data-level]) bool)
        list-result
        (proposition/app (proposition/const* 'list/membership [zero])
                         bool list-empty value)
        option-result
        (proposition/app (proposition/const* 'option/membership [zero])
                         bool option-empty value)
        core #(-> (elaborate/core-expression checked %) :term)
        expected (:term (kernel/normalize checked
                                         (core (proposition/falsity))))]
    (doseq [alias (vals prelude/inductive-membership-constant-aliases)]
      (is (string? (environment/resolve-id checked alias))))
    (is (= expected (:term (kernel/normalize checked (core list-result)))))
    (is (= expected (:term (kernel/normalize checked (core option-result)))))))

(deftest dependent-sum-projections-compute-for-sigma-and-psigma
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes
                    prelude/extend-inductive-memberships
                    prelude/extend-dependent-sums)
        zero [:zero]
        one [:succ zero]
        bool (proposition/const* 'data/Bool [])
        family (proposition/lam [['ignored bool]] bool)
        first-value (proposition/const* 'data/true [])
        second-value (proposition/const* 'data/false [])
        sigma-value
        (proposition/app (proposition/const* 'data/sigma [zero zero])
                         bool family first-value second-value)
        psigma-value
        (proposition/app (proposition/const* 'data/psigma [one one])
                         bool family first-value second-value)
        applications
        [[(proposition/app (proposition/const* 'sigma/first [zero zero])
                           bool family sigma-value)
          first-value]
         [(proposition/app (proposition/const* 'sigma/second [zero zero])
                           bool family sigma-value)
          second-value]
         [(proposition/app (proposition/const* 'psigma/first [one one])
                           bool family psigma-value)
          first-value]
         [(proposition/app (proposition/const* 'psigma/second [one one])
                           bool family psigma-value)
          second-value]]
        core #(-> (elaborate/core-expression checked %) :term)]
    (doseq [alias (vals prelude/dependent-sum-constant-aliases)]
      (is (string? (environment/resolve-id checked alias))))
    (doseq [[expression expected] applications]
      (is (= (core expected)
             (:term (kernel/normalize checked (core expression))))))))

(deftest set-function-layer-checks-and-pi-map-computes
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes
                    prelude/extend-inductive-memberships
                    prelude/extend-dependent-sums
                    prelude/extend-set-functions)
        one [:succ [:zero]]
        bool (proposition/const* 'data/Bool [])
        family (proposition/lam [['ignored bool]] bool)
        mapping
        (proposition/lam [['index bool] ['value bool]] 'value)
        source (proposition/lam [['index bool]]
                                (proposition/const* 'data/true []))
        expression
        (proposition/app (proposition/const* 'function/pi-map [one one one])
                         bool family family mapping source
                         (proposition/const* 'data/false []))
        core #(-> (elaborate/core-expression checked %) :term)]
    (doseq [alias (vals prelude/set-function-constant-aliases)]
      (is (string? (environment/resolve-id checked alias))))
    (is (= (core (proposition/const* 'data/true []))
           (:term (kernel/normalize checked (core expression)))))))

(deftest finite-set-layer-is-constructive-list-cover-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes
                    prelude/extend-inductive-memberships
                    prelude/extend-dependent-sums
                    prelude/extend-set-functions
                    prelude/extend-finite-sets)]
    (doseq [alias (vals prelude/finite-set-constant-aliases)]
      (is (string? (environment/resolve-id checked alias)))
      (is (empty? (kernel/axioms checked alias))))))

(deftest finite-witness-search-constructs-an-empty-list-cover
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators
                    prelude/extend-subtypes
                    prelude/extend-inductive-memberships
                    prelude/extend-dependent-sums
                    prelude/extend-set-functions
                    prelude/extend-finite-sets)
        zero [:zero]
        bool (proposition/const* 'data/Bool [])
        empty-set (proposition/app (proposition/const* 'set/empty [zero]) bool)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/app (proposition/const* 'set/finite [zero])
                           bool empty-set)))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true
                 :native-focused-intro? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate (search/prove
                   (:state (proof/start checked target))
                   (assoc options :native-list-cover-witnesses? true))
        nil-id (environment/resolve-id checked 'data/nil)]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (some #(and (= :native-finite-witness
                       (get-in % [:strategy :source]))
                    (contains? (term/constants
                                (get-in % [:strategy :term]))
                               nil-id))
              (:attempts candidate)))
    (is (empty? (get-in candidate [:proof :proof/axioms])))))

(deftest list-cover-witness-search-composes-prefix-and-append-enumerations
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-collections)
        level [:succ [:zero]]
        bool (proposition/const* 'data/Bool [])
        list-of (proposition/app (proposition/const* 'data/List [level]) bool)
        equality (fn [left right]
                   (proposition/equality level list-of left right))
        exists-equal
        (fn [expected]
          (proposition/existence
           level list-of
           (proposition/lam [['candidate list-of]]
                            (equality 'candidate expected))))
        prefix-target
        (proposition/forall
         [['value bool] ['enumeration list-of]]
         (exists-equal
          (proposition/app (proposition/const* 'data/cons [level])
                           bool 'value 'enumeration)))
        append-target
        (proposition/forall
         [['left list-of] ['right list-of]]
         (exists-equal
          (proposition/app (proposition/const* 'list/append [level])
                           bool 'left 'right)))
        core #(-> (elaborate/core-expression checked %) :term)
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true :native-focused-intro? true
                 :native-list-cover-witnesses? true}
        results (mapv #(search/prove (:state (proof/start checked (core %)))
                                    options)
                      [prefix-target append-target])]
    (doseq [result results]
      (is (= :proved (:status result)) (pr-str result))
      (is (= :checked (get-in result [:kernel :status])))
      (is (empty? (get-in result [:proof :proof/axioms]))))
    (is (contains? (term/constants (get-in (first results)
                                           [:proof :proof/term]))
                   (environment/resolve-id checked 'data/cons)))
    (is (contains? (term/constants (get-in (second results)
                                           [:proof :proof/term]))
                   (environment/resolve-id checked 'list/append)))))

(deftest opt-in-bool-cases-prove-dichotomy-as-inductive-proof-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment)
        bool (proposition/const* 'data/Bool [])
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['value bool]]
           (proposition/disjunction
            (proposition/equality [:succ [:zero]] bool 'value
                                  (proposition/const* 'data/false []))
            (proposition/equality [:succ [:zero]] bool 'value
                                  (proposition/const* 'data/true []))))))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate (search/prove (:state (proof/start checked target))
                                (assoc options :native-bool-cases? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (some #(= :induction (get-in % [:strategy :tactic]))
              (:attempts candidate)))))

(deftest bool-cases-use-derived-constructor-discrimination
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-collections)
        bool (proposition/const* 'data/Bool [])
        bool-not (fn [value]
                   (proposition/app
                    (proposition/const* 'bool/not []) value))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['left bool] ['right bool]
            ['same-output
             (proposition/equality
              [:succ [:zero]] bool
              (bool-not 'left) (bool-not 'right))]]
           (proposition/equality [:succ [:zero]] bool 'left 'right))))
        result
        (search/prove
         (:state (proof/start checked target))
         {:states 32 :depth 64 :wall-ms 2000
          :native-logic-focus? true :native-logic-prune? true
          :native-reducible-focus? true :native-bool-cases? true})]
    (is (= :proved (:status result)) (pr-str result))
    (is (= :checked (get-in result [:kernel :status])))
    (is (some #(= :native-constructor-discrimination
                  (get-in % [:strategy :source]))
              (:attempts result)))
    (is (empty? (get-in result [:proof :proof/axioms])))))

(deftest focused-introduction-preserves-existence-for-finite-witness-search
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-collections)
        bool (proposition/const* 'data/Bool [])
        bool-not (fn [value]
                   (proposition/app
                    (proposition/const* 'bool/not []) value))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['target bool]]
           (proposition/existence
            [:succ [:zero]] bool
            (proposition/lam
             [['source bool]]
             (proposition/equality
              [:succ [:zero]] bool (bool-not 'source) 'target))))))
        baseline-options
        {:states 32 :depth 64 :wall-ms 2000
         :native-logic-focus? true :native-logic-prune? true
         :native-reducible-focus? true :native-bool-cases? true}
        baseline
        (search/prove (:state (proof/start checked target)) baseline-options)
        candidate
        (search/prove
         (:state (proof/start checked target))
         (assoc baseline-options
                :native-focused-intro? true
                :native-finite-witnesses? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (some :focused-target (map :strategy (:attempts candidate))))
    (is (some #(= :native-finite-witness
                  (get-in % [:strategy :source]))
              (:attempts candidate)))
    (is (empty? (get-in candidate [:proof :proof/axioms])))))

(deftest expanded-set-relations-are-an-explicit-reproducible-layer
  (let [base (-> (proposition/build-environment)
                 prelude/extend-environment
                 prelude/extend-combinators
                 prelude/extend-collections)
        aliases (vals prelude/expanded-set-constant-aliases)
        extended (prelude/extend-set-relations base)]
    (is (every? nil? (map #(environment/resolve-id base %) aliases)))
    (is (every? string? (map #(environment/resolve-id extended %) aliases)))
    (is (= (count aliases) (count prelude/expanded-set-spec-names)))))

(deftest set-operators-are-isolated-behind-their-explicit-layer
  (let [base (-> (proposition/build-environment)
                 prelude/extend-environment
                 prelude/extend-combinators
                 prelude/extend-collections
                 prelude/extend-set-relations)
        aliases (vals prelude/set-operator-constant-aliases)
        extended (prelude/extend-set-operators base)]
    (is (every? nil? (map #(environment/resolve-id base %) aliases)))
    (is (every? string? (map #(environment/resolve-id extended %) aliases)))
    (is (= 10 (count (set (map #(environment/resolve-id extended %)
                               aliases)))))
    (is (= 9 (- (count (:rainbow.environment/declarations extended))
                (count (:rainbow.environment/declarations base)))))))

(deftest finite-inductive-cases-prove-product-involution-as-recursor-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators
                    prelude/extend-collections
                    prelude/extend-set-relations
                    prelude/extend-set-operators
                    prelude/extend-set-structural
                    prelude/extend-data-combinators)
        level [:succ [:zero]]
        bool (proposition/const* 'data/Bool [])
        product (proposition/app
                 (proposition/const* 'data/Product [level level]) bool bool)
        swap (fn [value]
               (proposition/app
                (proposition/const* 'product/swap [[:zero] [:zero]])
                bool bool value))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['pair product]]
           (proposition/equality level product (swap (swap 'pair)) 'pair))))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true :native-focused-intro? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-inductive-cases? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (some #(= :native-inductive-cases
                  (get-in % [:strategy :source]))
              (:attempts candidate)))
    (is (empty? (get-in candidate [:proof :proof/axioms])))))

(deftest nativeization-uses-explicit-concept-mappings
  (let [extended (prelude/extend-environment (proposition/build-environment))
        aliases (merge mathlib-native/default-constant-aliases
                       prelude/constant-aliases)
        statement {:foreign/name "Example.natIdentity"
                   :foreign/value :redacted
                   :foreign/type-fingerprint "lean-hash64:fixture"
                   :foreign/universes []
                   :foreign/type
                   [:pi [:const "Nat" []]
                    [:app [:app [:app [:const "Eq" [[:succ [:zero]]]]
                                 [:const "Nat" []]]
                           [:bound 0]]
                     [:bound 0]]
                    :explicit]}
        result (mathlib-native/nativeize-statement-type
                extended statement {:constant-aliases aliases})]
    (is (= :nativeized (:status result)) (pr-str result))
    (is (= ["Eq" "Nat"] (:foreign/constants result)) (pr-str result))))

(deftest definition-aware-focus-eliminates-reducible-logical-data
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['left 'Prop] ['right 'Prop]
            ['exclusive
             (proposition/app
              (proposition/const* 'proposition/xor []) 'left 'right)]]
           (proposition/disjunction 'left 'right))))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true}
        baseline
        (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-reducible-focus? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (empty? (get-in candidate [:proof :proof/axioms])))))

(deftest definition-aware-focus-proves-reducible-equivalence-by-identity
  (let [checked (-> (proposition/build-environment)
                    prelude/extend-environment
                    prelude/extend-combinators)
        xor (fn [left right]
              (proposition/app
               (proposition/const* 'proposition/xor []) left right))
        native-negation
        (fn [value]
          (proposition/app
           (proposition/const* 'proposition/negation []) value))
        expansion
        (fn [left right]
          (proposition/disjunction
           (proposition/conjunction left (native-negation right))
           (proposition/conjunction right (native-negation left))))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['left 'Prop] ['right 'Prop]]
           (proposition/app
            (proposition/const* 'proposition/equivalence [])
            (xor 'left 'right) (expansion 'left 'right)))))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-reducible-focus? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (empty? (get-in candidate [:proof :proof/axioms])))))
