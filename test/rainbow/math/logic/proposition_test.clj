(ns rainbow.math.logic.proposition-test
  (:require [clojure.test :refer :all]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.proof :as proof]
            [rainbow.search :as search]))

(def checked-environment (delay (proposition/build-environment)))

(defn leading-binder-modes [term]
  (loop [term term modes []]
    (if (contains? #{:pi :lam} (first term))
      (recur (nth term 2) (conj modes (nth term 3)))
      modes)))

(deftest native-connectives-and-combinators-are-axiom-free-proof-data
  (let [report (proposition/report)]
    (is (= :passed (:status report)))
    (is (= '[proposition/truth proposition/falsity
             proposition/conjunction proposition/equivalence
             proposition/negation equality/inequality proposition/disjunction
             proposition/existence proposition/unique-existence]
           (:connectives report)))
    (is (= 16 (count (:theorems report))))
    (is (every? empty? (vals (:axioms report))))
    (is (= :none (:trusted-base-change report)))))

(deftest every-proposition-declaration-rechecks-in-the-kernel
  (let [checked-environment @checked-environment]
    (doseq [name (concat (map :name proposition/connective-specs)
                         (map :name proposition/theorem-specs))]
      (let [declaration
            (environment/declaration
             checked-environment
             (environment/resolve-id checked-environment name))]
        (is (= :checked
               (:status
                (kernel/check checked-environment
                              (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))
            (str name " must recheck"))))))

(deftest elaboration-preserves-optional-binder-modes
  (let [checked-environment @checked-environment
        declaration
        (environment/declaration
         checked-environment
         (environment/resolve-id
          checked-environment 'proposition/equivalence-congruence))
        invalid
        (elaborate/type-expression
         (proposition/forall [['value 'Prop :instance]] 'Prop))]
    (is (= [:implicit :implicit :implicit :implicit :explicit :explicit]
           (leading-binder-modes (:rainbow/type declaration))))
    (is (= [:implicit :implicit :implicit :implicit :explicit :explicit]
           (leading-binder-modes (:rainbow/value declaration))))
    (is (= :rejected (:status invalid)))
    (is (= :elaborate/invalid-forall
           (get-in invalid [:error :error/category])))
    (is (empty? (kernel/axioms checked-environment
                               (:rainbow/id declaration))))))

(deftest search-stops-apply-at-a-reducible-falsity-conclusion
  (let [checked-environment @checked-environment
        target
        (:term
         (elaborate/core-expression
          checked-environment
          (proposition/forall
           [['A 'Prop] ['B 'Prop]
            ['function (proposition/arrow 'A 'B)]
            ['not-b (proposition/negation 'B)]]
           (proposition/negation 'A))))
        started (proof/start checked-environment target)
        result (search/prove (:state started))]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (false? (proof/contains-holes?
                 (get-in result [:proof :proof/term]))))))

(deftest search-kernel-infers-dependent-local-application-prefixes
  (let [checked-environment @checked-environment
        target
        (:term
         (elaborate/core-expression
          checked-environment
          (proposition/forall
           [['A proposition/sort-u]
            ['P (proposition/arrow 'A 'Prop)]
            ['Q (proposition/arrow 'A 'Prop)]
            ['pointwise
             (proposition/forall
              [['x 'A]
               ['evidence (proposition/app 'P 'x)]]
              (proposition/app 'Q 'x))]
            ['all-p
             (proposition/forall
              [['x 'A]] (proposition/app 'P 'x))]
            ['x 'A]]
           (proposition/app 'Q 'x))))
        started (proof/start checked-environment target {:universes ['u]})
        result (search/prove (:state started)
                             {:local-application-depth 4
                              :local-application-terms 128})]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (pos? (get-in result [:telemetry
                              :local-application-candidates])))
    (is (false? (proof/contains-holes?
                 (get-in result [:proof :proof/term]))))))

(deftest focused-native-logic-search-constructs-and-eliminates-conjunction
  (let [checked-environment @checked-environment
        target
        (:term
         (elaborate/core-expression
          checked-environment
          (proposition/forall
           [['A 'Prop] ['B 'Prop]
            ['evidence (proposition/conjunction 'A 'B)]]
           (proposition/conjunction 'B 'A))))
        baseline (search/prove
                  (:state (proof/start checked-environment target))
                  {:states 256 :depth 32 :wall-ms 2000})
        focused (search/prove
                 (:state (proof/start checked-environment target))
                 {:states 256 :depth 32 :wall-ms 2000
                  :native-logic-focus? true
                  :native-logic-prune? true})]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status focused)))
    (is (= :checked (get-in focused [:kernel :status])))
    (is (pos? (get-in focused [:telemetry :native-logic-candidates])))
    (is (false? (proof/contains-holes?
                 (get-in focused [:proof :proof/term]))))))

(deftest focused-compositional-search-combines-equivalence-elimination
  (let [checked-environment @checked-environment
        target
        (:term
         (elaborate/core-expression
          checked-environment
          (proposition/forall
           [['A 'Prop] ['B 'Prop]
            ['equivalent (proposition/equivalence 'A 'B)]]
           (proposition/equivalence
            (proposition/negation 'A)
            (proposition/negation 'B)))))
        result
        (search/prove
         (:state (proof/start checked-environment target))
         {:states 512 :depth 64 :wall-ms 3000
          :local-application-depth 4 :local-application-terms 128
          :local-application-compositional? true
          :native-logic-focus? true :native-logic-prune? true})]
    (is (= :proved (:status result)))
    (is (= :checked (get-in result [:kernel :status])))
    (is (pos? (get-in result [:telemetry :native-logic-candidates])))
    (is (pos? (get-in result [:telemetry :local-application-candidates])))))

(deftest focused-native-logic-rewrites-equality-before-negation-introduction
  (let [checked-environment @checked-environment
        target
        (:term
         (elaborate/core-expression
          checked-environment
          (proposition/forall
           [['A proposition/sort-u]
            ['left 'A] ['middle 'A] ['right 'A]
            ['equal
             (proposition/equality proposition/U 'A 'left 'middle)]
            ['different
             (proposition/inequality proposition/U 'A 'middle 'right)]]
           (proposition/inequality proposition/U 'A 'left 'right))))
        baseline
        (search/prove
         (:state (proof/start checked-environment target {:universes ['u]}))
         {:states 256 :depth 32 :wall-ms 2000
          :local-application-depth 4 :local-application-terms 128
          :local-application-compositional? true})
        focused
        (search/prove
         (:state (proof/start checked-environment target {:universes ['u]}))
         {:states 256 :depth 32 :wall-ms 2000
          :local-application-depth 4 :local-application-terms 128
          :local-application-compositional? true
          :native-logic-focus? true :native-logic-prune? true
          :native-equality-rewrite? true})]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status focused)))
    (is (= :checked (get-in focused [:kernel :status])))
    (is (pos? (get-in focused [:telemetry :native-logic-candidates])))
    (is (some #(= :rewrite (get-in % [:strategy :tactic]))
              (:attempts focused)))))
