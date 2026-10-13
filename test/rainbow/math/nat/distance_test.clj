(ns rainbow.math.nat.distance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.distance :as nat-distance]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Day-86 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          finset-range/extend-environment
          nat-distance/extend-environment))))

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

(deftest computational-distance-package-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        definitions (nat-distance/definition-ids checked-environment)
        theorems (nat-distance/theorem-ids checked-environment)]
    (is (= #{'algebra/heterogeneous-add
             'algebra/homogeneous-add-instance
             'nat/distance}
           (set (keys definitions))))
    (is (= #{'nat/distance-successor
             'nat/distance-commutative
             'nat/distance-add-left
             'nat/distance-add-right
             'nat/distance-right-bound
             'nat/distance-left-bound}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest evaluator-computes-structural-natural-distance
  (let [checked-environment @checked-environment
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        four [:app successor three]
        expression [:app [:const 'nat/distance []] four one]
        normalized (kernel/normalize checked-environment
                                     (core checked-environment expression))]
    (is (= :normalized (:status normalized)))
    (is (= (core checked-environment three) (:term normalized)))))
