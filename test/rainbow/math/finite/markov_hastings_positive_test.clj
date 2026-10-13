(ns rainbow.math.finite.markov-hastings-positive-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-hastings-positive :as positive]))

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

(deftest positive-hastings-flow-and-transition-are-kernel-checked-and-axiom-free
  (let [env @checked-environment]
    (is (empty? (positive/definition-ids env)))
    (is (= #{'mcmc/nnrat-hastings-ratio-acceptance-positive
             'mcmc/nnrat-hastings-accepted-flow-positive
             'mcmc/nnrat-hastings-accepted-transition-positive
             'mcmc/nnrat-hastings-completed-kernel-positive
             'mcmc/nnrat-hastings-canonical-kernel-positive}
           (set (keys (positive/theorem-ids env)))))
    (doseq [alias (keys (positive/theorem-ids env))]
      (is (checked? env alias) (str alias))
      (is (= #{} (kernel/axioms env (environment/resolve-id env alias)))
          (str alias)))))
