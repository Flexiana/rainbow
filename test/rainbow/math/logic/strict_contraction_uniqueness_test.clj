(ns rainbow.math.logic.strict-contraction-uniqueness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.strict-contraction-uniqueness :as uniqueness]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/finite-metric-separation/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Finite metric-separation checkpoint rejected"
                        {:checkpoint checkpoint})))
      (uniqueness/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest strict-contraction-uniqueness-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (uniqueness/theorem-ids checked-environment)]
    (is (= #{'nat/equal-zero-of-not-positive
             'list/nat-map-max-congruent-on
             'metric/finite-sup-congruent-on
             'metric/strict-contraction-fixed-points-have-zero-sup-distance
             'metric/strict-contraction-fixed-points-unique-on-support}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-fixed-point-uniqueness-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment
         'metric/strict-contraction-fixed-points-unique-on-support)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
