(ns rainbow.math.rational.nnrat.finite-min-positive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.finite-min-positive :as finite-min]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (finite-min/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-minimum-of-positive-rationals-is-a-positive-lower-bound
  (let [env @checked-environment
        definitions (finite-min/definition-ids env)
        theorems (finite-min/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'nnrat/min-ub-positive
             'nnrat/min-ub-positive-lower-bound
             'nnrat/le-all-member
             'nnrat/min-ub-below-member}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
