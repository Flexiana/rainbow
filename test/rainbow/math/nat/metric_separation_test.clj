(ns rainbow.math.nat.metric-separation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.metric-separation :as separation]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/nat-distance-core-mathlib/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Nat-distance-core checkpoint rejected"
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

(deftest natural-metric-separation-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (separation/theorem-ids checked-environment)]
    (is (= #{'nat/positive-of-nonzero
             'nat/nonzero-of-positive
             'nat/distance-nonzero-of-not-equal
             'nat/distance-positive-of-not-equal
             'nat/distance-positive-equivalent-not-equal}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-positivity-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id checked-environment
                                'nat/positive-of-nonzero)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
