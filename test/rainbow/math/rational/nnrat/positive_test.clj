(ns rainbow.math.rational.nnrat.positive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.positive :as positive]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (positive/extend-environment (:environment checkpoint)))))

(defn- checked? [env alias]
  (let [id (environment/resolve-id env alias)
        declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest exact-nnrat-positivity-is-kernel-checked-and-axiom-free
  (let [env @checked-environment]
    (is (= #{'nnrat/positive}
           (set (keys (positive/definition-ids env)))))
    (is (= #{'nnrat/one-positive
             'nnrat/multiply-positive
             'nnrat/positive-respects-equivalence
             'nat/add-positive-left
             'nnrat/denominator-positive 'nnrat/add-positive-left
             'nnrat/add-positive-right
             'nnrat/min-positive
             'nnrat/reciprocal-positive 'nnrat/divide-positive-left}
           (set (keys (positive/theorem-ids env)))))
    (doseq [alias (concat (keys (positive/definition-ids env))
                          (keys (positive/theorem-ids env)))]
      (is (checked? env alias) (str alias))
      (is (= #{} (kernel/axioms env (environment/resolve-id env alias)))
          (str alias)))))
