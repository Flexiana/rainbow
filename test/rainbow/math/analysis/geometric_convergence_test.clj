(ns rainbow.math.analysis.geometric-convergence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.analysis.geometric-convergence :as gc]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (gc/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest geometric-convergence-reaches-thresholds-axiom-free
  (let [env @checked-environment
        theorems (gc/theorem-ids env)]
    (is (= #{'convergence/reaches-one-at-step-3
             'convergence/reaches-half-at-step-4
             'convergence/monotone-decrease
             'convergence/reaches-below-half-at-step-5}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))
