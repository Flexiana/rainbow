(ns rainbow.math.linear.vector.convex-combination-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.vector.convex-combination :as convex]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "AHoF D63 checkpoint rejected"
                        {:checkpoint checkpoint})))
      (convex/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest normalized-vector-convex-combinations-preserve-intervals
  (let [checked-environment @checked-environment
        definitions (convex/definition-ids checked-environment)
        theorems (convex/theorem-ids checked-environment)]
    (is (= #{'vector/nnrat-wsum2}
           (set (keys definitions))))
    (is (= #{'signed/scale-additive-rate
             'signed/scale-one
             'signed/scale-respects-rate-equivalence
             'vector/scale-additive-rate
             'vector/scale-one
             'vector/scale-respects-rate-equivalence
             'vector/nnrat-wsum2-monotone
             'vector/nnrat-wsum2-normalized-repeated
             'vector/nnrat-convex-lower-bound
             'vector/nnrat-convex-upper-bound}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (kernel-checked? checked-environment id) (str name)))))
