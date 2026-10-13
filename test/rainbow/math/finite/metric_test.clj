(ns rainbow.math.finite.metric-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance :as milestone]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
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
          finite-metric/extend-environment))))

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

(deftest finite-sup-package-is-native-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        definitions (finite-metric/definition-ids checked-environment)
        theorems (finite-metric/theorem-ids checked-environment)]
    (is (= #{'nat/recursive-max
             'list/nat-map-max
             'metric/finite-sup-distance}
           (set (keys definitions))))
    (is (= #{'nat/recursive-max-left-bound
             'nat/recursive-max-right-bound
             'nat/recursive-max-commutative
             'nat/recursive-max-is-left-or-right
             'nat/recursive-max-least-upper-bound
             'list/nat-map-max-upper-bound
             'list/nat-map-max-bounded
             'list/nat-map-max-congruent
             'metric/finite-sup-upper-bound
             'metric/finite-sup-symmetric
             'metric/finite-sup-triangle}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest evaluator-computes-finite-sup-distance
  (let [checked-environment @checked-environment
        nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        source [:app [:const 'finset-data/range []] three]
        identity [:fn [['state nat]] 'state]
        zero-function [:fn [['state nat]] zero]
        expression
        [:app [:const 'metric/finite-sup-distance [[:zero]]]
         nat source identity zero-function]
        result
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    (is (= :normalized (:status result)))
    (is (= (core checked-environment two) (:term result)))))
