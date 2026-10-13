(ns rainbow.math.sets.preimage-lattice-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.sets.preimage-lattice :as preimage]))

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

(deftest preimages-preserve-binary-set-operations
  (let [checked-environment @checked-environment
        theorems (preimage/theorem-ids checked-environment)]
    (is (= #{'set/preimage-intersection-subset-intersection-preimages
             'set/intersection-preimages-subset-preimage-intersection
             'set/preimage-intersection-equivalent-intersection-preimages
             'set/preimage-union-subset-union-preimages
             'set/union-preimages-subset-preimage-union
             'set/preimage-union-equivalent-union-preimages
             'set/preimage-difference-subset-difference-preimages
             'set/difference-preimages-subset-preimage-difference
             'set/preimage-difference-equivalent-difference-preimages}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
