(ns rainbow.math.sets.preimage-composition-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.preimage-composition :as preimage]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (preimage/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest preimages-respect-identity-and-composition
  (let [checked-environment @checked-environment
        theorems (preimage/theorem-ids checked-environment)]
    (is (= #{'set/preimage-identity-subset-source
             'set/source-subset-preimage-identity
             'set/preimage-identity-equivalent-source
             'set/preimage-compose-subset-nested-preimage
             'set/nested-preimage-subset-preimage-compose
             'set/preimage-compose-equivalent-nested-preimage}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
