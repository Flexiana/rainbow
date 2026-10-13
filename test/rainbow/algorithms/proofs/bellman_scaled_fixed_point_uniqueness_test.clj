(ns rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness
             :as uniqueness]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/strict-contraction-uniqueness/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Strict-contraction checkpoint rejected"
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

(deftest bellman-scaled-fixed-point-uniqueness-is-axiom-free-and-checked
  (let [checked-environment @checked-environment
        ids (uniqueness/theorem-ids checked-environment)]
    (is (= #{'nat/at-most-antisymmetric
             'nat/at-most-strict-below-transitive
             'nat/positive-right-of-strict-below
             'nat/multiply-right-strict-monotone-positive
             'nat/recursive-max-multiply-left
             'list/nat-map-max-multiply-left
             'metric/finite-sup-distance-multiply-left
             'metric/scaled-contraction-scaled-fixed-points-have-zero-sup-distance
             'bellman/fixed-policy-scaled-fixed-points-have-zero-sup-distance
             'bellman/fixed-policy-scaled-fixed-points-unique-on-support}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-bellman-uniqueness-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment
         'bellman/fixed-policy-scaled-fixed-points-unique-on-support)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
