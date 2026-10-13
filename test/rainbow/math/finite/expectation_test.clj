(ns rainbow.math.finite.expectation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          finset-data/extend-environment
          finite-expectation/extend-environment))))

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
      (throw (ex-info "Test expression failed elaboration" {:result result})))
    (:term result)))

(deftest finite-mass-and-expectation-are-axiom-free-proof-data
  (let [checked-environment @checked-environment
        definitions (finite-expectation/definition-ids checked-environment)
        theorems (finite-expectation/theorem-ids checked-environment)]
    (is (= #{'nat/multiply 'list/nat-map-sum
             'probability/weight-total 'probability/normalized-at
             'probability/expectation-numerator}
           (set (keys definitions))))
    (is (= #{'list/nat-map-sum-zero
             'probability/expectation-zero 'nat/one-times 'nat/times-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest rainbow-evaluator-computes-an-exact-two-state-expectation-numerator
  (let [checked-environment @checked-environment
        nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        range-two [:app [:const 'finset-data/range []] two]
        unit-mass [:fn [['state nat]] one]
        identity-value [:fn [['state nat]] 'state]
        expression
        [:app [:const 'probability/expectation-numerator [[:zero]]]
         nat range-two unit-mass identity-value]
        normalized
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    (is (= :normalized (:status normalized)))
    (is (= (core checked-environment one) (:term normalized)))))
