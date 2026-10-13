(ns rainbow.math.rational.bellman-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.rational-expectation :as expectation]
            [rainbow.math.nat.semiring :as nat-semiring]
            [rainbow.math.nonnegative-rational :as nnrat]
            [rainbow.math.rational.bellman :as bellman]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/or-contraction/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "OR contraction checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          nat-semiring/extend-environment
          nnrat/extend-environment
          expectation/extend-environment
          bellman/extend-environment))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Rational Bellman test expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(deftest rational-fixed-policy-bellman-is-generic-native-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (bellman/definition-ids checked-environment)
        theorems (bellman/theorem-ids checked-environment)]
    (is (= #{'bellman/nnrat-fixed-policy
             'bellman/nnrat-value-iterate
             'or-example/nnrat-deterministic-transition
             'or-example/nnrat-identity-reward
             'or-example/nnrat-zero-value
             'or-example/nnrat-step-one-value
             'or-example/nnrat-two-step-value}
           (set (keys definitions))))
    (is (= #{'bellman/two-state-first-step-zero
             'bellman/two-state-first-step-one
             'bellman/two-state-compact-second-step-zero
             'bellman/two-state-compact-second-step-one
             'probability/two-state-step-one-expectation-zero
             'probability/two-state-step-one-expectation-one
             'bellman/two-state-second-continuation-zero-congruent
             'bellman/two-state-second-continuation-one-congruent
             'bellman/two-state-second-step-zero-congruent
             'bellman/two-state-second-step-one-congruent
             'bellman/nnrat-fixed-policy-unfold
             'bellman/nnrat-value-iterate-zero
             'bellman/nnrat-fixed-policy-congruent
             'bellman/two-state-two-step-value-iteration}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest evaluator-computes-both-proved-two-step-values
  (let [checked-environment @checked-environment
        nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        make-rational [:const 'nnrat/make []]
        computed [:const 'or-example/nnrat-two-step-value []]
        numerator [:const 'nnrat/numerator []]
        denominator [:const 'nnrat/denominator []]
        multiply [:const 'nat/multiply []]
        evaluation-budget {:reductions 1000000}
        expected [[zero [:const 'nnrat/zero []]]
                  [one [:app make-rational three one]]]]
    (doseq [[state value] expected]
      (let [actual [:app computed state]
            left-cross
            [:app multiply [:app numerator actual] [:app denominator value]]
            right-cross
            [:app multiply [:app numerator value] [:app denominator actual]]
            normalized-left
            (kernel/normalize checked-environment
                              (core checked-environment left-cross)
                              evaluation-budget)
            normalized-right
            (kernel/normalize checked-environment
                              (core checked-environment right-cross)
                              evaluation-budget)]
        (is (= :normalized (:status normalized-left)))
        (is (= :normalized (:status normalized-right)))
        (is (= (:term normalized-left) (:term normalized-right)))))))
