(ns rainbow.math.logic.classical-test
  (:require [clojure.test :refer :all]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.classical :as classical]
            [rainbow.math.prelude :as prelude]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.proof :as proof]
            [rainbow.search :as search]))

(def extension
  (delay
    (classical/extend-activation
     (profile/activate (proposition/build-environment) :classical))))

(deftest classical-theorems-are-proof-data-with-one-explicit-axiom
  (let [{:keys [environment activation declarations]} @extension
        excluded-middle-id (first (:logical/axiom-ids activation))]
    (is (= 4 (count declarations)))
    (doseq [declaration declarations]
      (is (= :theorem (:rainbow/kind declaration)))
      (is (= #{excluded-middle-id}
             (kernel/axioms environment (:rainbow/id declaration))))
      (is (= :checked
             (:status (kernel/check environment
                                    (:rainbow/value declaration)
                                    (:rainbow/type declaration)
                                    #{})))))))

(deftest classical-derivations-refuse-a-constructive-environment
  (let [data
        (try
          (classical/extend-activation
           (profile/activate (proposition/build-environment) :constructive))
          (catch clojure.lang.ExceptionInfo exception (ex-data exception)))]
    (is (= :classical/missing-profile (:error/category data)))))

(deftest focused-classical-cases-proves-double-negation-at-fixed-budget
  (let [checked (:environment @extension)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['claim 'Prop]
            ['not-not-claim
             (proposition/negation (proposition/negation 'claim))]]
           'claim)))
        options {:states 32 :depth 64 :wall-ms 2000
                 :local-application-depth 4
                 :local-application-terms 128
                 :local-application-compositional? true
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-classical-cases? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (= (:logical/axiom-ids (:activation @extension))
           (get-in candidate [:proof :proof/axioms])))
    (is (some #(= :classical-proof-plan (get-in % [:strategy :source]))
              (:attempts candidate)))))

(deftest tautology-compiler-emits-one-checked-excluded-middle-proof
  (let [checked (:environment @extension)
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['claim 'Prop]]
           (proposition/disjunction 'claim
                                    (proposition/negation 'claim)))))
        options {:states 8 :depth 16 :wall-ms 1000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-classical-tautology? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (= (:logical/axiom-ids (:activation @extension))
           (get-in candidate [:proof :proof/axioms])))
    (is (= 1 (some #(get-in % [:strategy :tautology/atom-count])
                   (:attempts candidate))))))

(deftest tautology-compiler-proves-two-atom-xor-equivalence
  (let [checked (-> (:environment @extension)
                    prelude/extend-environment
                    prelude/extend-combinators)
        app-constant
        (fn [alias & arguments]
          (apply proposition/app (proposition/const* alias []) arguments))
        equivalent (fn [left right]
                     (app-constant 'proposition/equivalence left right))
        xor (fn [left right]
              (app-constant 'proposition/xor left right))
        negate (fn [value]
                 (app-constant 'proposition/negation value))
        target
        (:term
         (elaborate/core-expression
          checked
          (proposition/forall
           [['left 'Prop] ['right 'Prop]]
           (equivalent (xor 'left 'right)
                       (negate (equivalent 'left 'right))))))
        options {:states 32 :depth 64 :wall-ms 2000
                 :native-logic-focus? true :native-logic-prune? true
                 :native-reducible-focus? true}
        baseline (search/prove (:state (proof/start checked target)) options)
        candidate
        (search/prove (:state (proof/start checked target))
                      (assoc options :native-classical-tautology? true))]
    (is (= :blocked (:status baseline)))
    (is (= :proved (:status candidate)) (pr-str candidate))
    (is (= :checked (get-in candidate [:kernel :status])))
    (is (= (:logical/axiom-ids (:activation @extension))
           (get-in candidate [:proof :proof/axioms])))
    (is (= 2 (some #(get-in % [:strategy :tautology/atom-count])
                   (:attempts candidate))))))
