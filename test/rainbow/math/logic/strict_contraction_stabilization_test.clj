(ns rainbow.math.logic.strict-contraction-stabilization-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.strict-contraction-stabilization
             :as stabilization]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/bellman-scaled-fixed-point-uniqueness/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Bellman uniqueness checkpoint rejected"
                        {:checkpoint checkpoint})))
      (stabilization/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest strict-contraction-stabilization-is-axiom-free-and-checked
  (let [checked-environment @checked-environment
        ids (stabilization/theorem-ids checked-environment)]
    (is (= #{'nat/at-most-successor-cancel
             'nat/strict-below-of-strict-below-at-most-successor
             'nat/equal-zero-or-positive
             'function/nat-iterate-zero
             'function/nat-iterate-successor
             'nat/strictly-descending-sequence-reaches-zero-within-bound
             'metric/strict-contraction-consecutive-iterate-distance-decreases
             'metric/strict-contraction-iterate-stabilizes-within-initial-distance
             'metric/strict-contraction-has-bounded-support-fixed-point}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-stabilization-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment
         'metric/strict-contraction-has-bounded-support-fixed-point)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
