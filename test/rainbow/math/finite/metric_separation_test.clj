(ns rainbow.math.finite.metric-separation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.metric-separation :as separation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/nat-metric-separation-mathlib/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Nat metric-separation checkpoint rejected"
                        {:checkpoint checkpoint})))
      (separation/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-sup-metric-separation-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (separation/theorem-ids checked-environment)]
    (is (= #{'nat/equal-zero-of-at-most-zero
             'list/nat-map-max-zero-of-memberwise-zero
             'metric/finite-sup-zero-of-pointwise-equal
             'metric/pointwise-equal-of-finite-sup-zero
             'metric/finite-sup-zero-equivalent-pointwise-equal
             'metric/finite-sup-positive-of-pointwise-not-equal}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-finite-sup-separation-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment
         'metric/finite-sup-zero-equivalent-pointwise-equal)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
