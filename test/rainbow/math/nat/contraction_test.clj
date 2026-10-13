(ns rainbow.math.nat.contraction-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance :as milestone]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.contraction :as contraction]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Nat order/metric checkpoint rejected"
                        {:checkpoint checkpoint})))
      (contraction/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest multiplicative-distance-laws-are-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (contraction/theorem-ids checked-environment)]
    (is (= #{'nat/multiply-successor-right
             'nat/multiply-commutative
             'nat/distance-multiply-right
             'nat/distance-multiply-left
             'nat/at-most-rewrite-right
             'list/nat-map-sum-distance-bound
             'nat/at-most-rewrite-left
             'list/nat-map-sum-distance-bound-by
             'list/nat-map-sum-multiply-right
             'probability/expectation-distance-bound}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
