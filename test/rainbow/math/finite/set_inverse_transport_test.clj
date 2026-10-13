(ns rainbow.math.finite.set-inverse-transport-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set-inverse-transport :as transport]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (transport/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest explicit-set-inverses-transport-finiteness-constructively
  (let [checked-environment @checked-environment
        theorems (transport/theorem-ids checked-environment)]
    (is (= #{'set/nonempty-of-maps-to
             'set/nonempty-equivalent-of-mutual-maps
             'set/finite-equivalent-of-inverse
             'set/infinite-equivalent-of-inverse
             'set/finite-nonempty-equivalent-of-inverse}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
