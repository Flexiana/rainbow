(ns rainbow.math.constructive-unique-fixed-point-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.constructive-unique-fixed-point :as unique]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/strict-contraction-stabilization/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Stabilization checkpoint rejected"
                        {:checkpoint checkpoint})))
      (unique/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest constructive-unique-fixed-point-is-axiom-free-and-checked
  (let [checked-environment @checked-environment
        ids (unique/theorem-ids checked-environment)]
    (is (= #{'metric/strict-contraction-bounded-fixed-point-agrees-with-fixed-point
             'metric/strict-contraction-has-bounded-canonical-support-fixed-point
             'metric/strict-contraction-support-fixed-point-exists-and-is-unique}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))

(deftest malformed-constructive-unique-certificate-is-rejected
  (let [checked-environment @checked-environment
        theorem-id
        (environment/resolve-id
         checked-environment
         'metric/strict-contraction-support-fixed-point-exists-and-is-unique)
        theorem (environment/declaration checked-environment theorem-id)
        zero-id (environment/resolve-id checked-environment 'data/zero)
        result
        (kernel/check checked-environment [:const zero-id []]
                      (:rainbow/type theorem)
                      (set (:rainbow/universes theorem)))]
    (is (= :rejected (:status result)))))
