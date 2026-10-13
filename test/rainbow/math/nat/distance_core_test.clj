(ns rainbow.math.nat.distance-core-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.distance-core :as distance-core]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/or-rational-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "OR rational checkpoint rejected"
                        {:checkpoint checkpoint})))
      (distance-core/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest natural-distance-core-is-axiom-free-and-kernel-checked
  (let [checked-environment @checked-environment
        ids (distance-core/theorem-ids checked-environment)]
    (is (= #{'nat/distance-zero-left
             'nat/distance-zero-right
             'nat/distance-self
             'nat/equal-of-distance-zero
             'nat/distance-zero-of-equal
             'nat/distance-zero-equivalent-equal}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-distance-self-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id checked-environment 'nat/distance-self)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment
                      [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
