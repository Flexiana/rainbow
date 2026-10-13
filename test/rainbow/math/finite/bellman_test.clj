(ns rainbow.math.finite.bellman-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman :as finite-bellman]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.order :as nat-order]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          finset-data/extend-environment
          finite-expectation/extend-environment
          nat-order/extend-environment
          finite-bellman/extend-environment))))

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

(deftest transition-and-bellman-capability-is-axiom-free
  (let [checked-environment @checked-environment
        definitions (finite-bellman/definition-ids checked-environment)
        theorems (finite-bellman/theorem-ids checked-environment)]
    (is (= #{'markov/row-total 'markov/rows-normalized-at
             'bellman/output-scale 'bellman/fixed-policy-numerator
             'or-example/two-state-space 'or-example/uniform-mass
             'or-example/uniform-transition 'or-example/identity-value}
           (set (keys definitions))))
    (is (= #{'probability/two-state-uniform-normalized
             'probability/two-state-identity-expectation
             'markov/two-state-rows-normalized
             'bellman/two-state-state-one-result
             'bellman/zero-data 'bellman/zero-discount
             'bellman/fixed-policy-monotone}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest rainbow-evaluator-computes-the-proved-bellman-numerator
  (let [checked-environment @checked-environment
        nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        four [:app successor three]
        five [:app successor four]
        expression
        [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
         nat two
         [:const 'or-example/two-state-space []]
         [:const 'or-example/uniform-transition []]
         [:const 'or-example/identity-value []]
         one [:const 'or-example/identity-value []] one]
        normalized
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    (is (= :normalized (:status normalized)))
    (is (= (core checked-environment five) (:term normalized)))
    (is (some? (environment/resolve-id
                checked-environment 'bellman/two-state-state-one-result)))))
