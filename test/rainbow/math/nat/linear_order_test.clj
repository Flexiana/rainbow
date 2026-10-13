(ns rainbow.math.nat.linear-order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.finite-nat :as finite-nat]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.nat.distance :as nat-distance]
            [rainbow.math.nat.linear-order :as linear-order]
            [rainbow.math.nat.metric :as nat-metric]
            [rainbow.math.nat.order :as nat-order]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint finite-nat/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Finite-Nat checkpoint rejected"
                        {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finite-expectation/extend-environment
          nat-order/extend-environment
          nat-distance/extend-environment
          nat-metric/extend-environment
          linear-order/extend-environment))))

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

(defn- normalize [checked-environment expression]
  (kernel/normalize checked-environment
                    (core checked-environment expression)))

(deftest computational-linear-order-data-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (linear-order/definition-ids checked-environment)]
    (is (= 15 (count ids)))
    (is (string? (linear-order/block-id checked-environment)))
    (is (= checked-environment
           (linear-order/extend-environment checked-environment)))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))
    (doseq [name '[order/Ordering order/less order/equal order/greater]]
      (is (= #{} (kernel/axioms checked-environment name)) (str name)))))

(deftest evaluator-computes-min-max-decisions-and-ordering
  (let [checked-environment @checked-environment
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        four [:app successor three]
        five [:app successor four]
        evaluates-to?
        (fn [expression expected]
          (let [result (normalize checked-environment expression)]
            (and (= :normalized (:status result))
                 (= (core checked-environment expected) (:term result)))))]
    (is (evaluates-to? [:app [:const 'nat/min []] three five] three))
    (is (evaluates-to? [:app [:const 'nat/max []] three five] five))
    (is (evaluates-to? [:app [:const 'nat/decide-at-most []] three five]
                       [:const 'data/true []]))
    (is (evaluates-to? [:app [:const 'nat/decide-at-most []] five three]
                       [:const 'data/false []]))
    (is (evaluates-to? [:app [:const 'nat/ordering []] two five]
                       [:const 'order/less []]))
    (is (evaluates-to? [:app [:const 'nat/ordering []] three three]
                       [:const 'order/equal []]))
    (is (evaluates-to? [:app [:const 'nat/ordering []] five two]
                       [:const 'order/greater []]))))
