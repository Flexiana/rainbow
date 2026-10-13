(ns rainbow.algorithms.proofs.bellman-contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance :as milestone]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.bellman-contraction :as bellman-contraction]
            [rainbow.math.finite.bellman :as finite-bellman]
            [rainbow.math.finite.metric :as finite-metric]
            [rainbow.math.nat.contraction :as contraction]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Nat order/metric checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          contraction/extend-environment
          finite-metric/extend-environment
          finite-bellman/extend-environment
          bellman-contraction/extend-environment))))

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

(deftest bellman-contraction-chain-is-native-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        theorems (bellman-contraction/theorem-ids checked-environment)]
    (is (= #{'list/nat-map-sum-distance-bound-by-on
             'probability/expectation-distance-bound-on
             'bellman/fixed-policy-pointwise-contraction
             'bellman/fixed-policy-sup-contraction
             'bellman/two-state-contraction-example}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest evaluator-computes-the-two-state-output-distance
  (let [checked-environment @checked-environment
        nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        source [:const 'or-example/two-state-space []]
        transition [:const 'or-example/uniform-transition []]
        reward [:const 'or-example/identity-value []]
        left [:const 'or-example/identity-value []]
        right [:fn [['state nat]] zero]
        left-bellman
        [:fn [['state nat]]
         [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
          nat two source transition reward one left 'state]]
        right-bellman
        [:fn [['state nat]]
         [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
          nat two source transition reward one right 'state]]
        expression
        [:app [:const 'metric/finite-sup-distance [[:zero]]]
         nat source left-bellman right-bellman]
        result
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    (is (= :normalized (:status result)))
    (is (= (core checked-environment one) (:term result)))
    (is (some? (environment/resolve-id
                checked-environment
                'bellman/two-state-contraction-example)))))
