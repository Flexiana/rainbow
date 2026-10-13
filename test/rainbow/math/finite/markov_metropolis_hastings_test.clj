(ns rainbow.math.finite.markov-metropolis-hastings-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-metropolis-hastings :as mh]
            [rainbow.algorithms.reference.finite-metropolis-hastings :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (mh/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-metropolis-hastings-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (mh/definition-ids env)
        theorems (mh/theorem-ids env)]
    (is (= #{'mcmc/mh-two-state-space
             'mcmc/mh-target-mass
             'mcmc/mh-independence-proposal
             'mcmc/mh-acceptance
             'mcmc/mh-kernel}
           (set (keys definitions))))
    (is (= #{'mcmc/mh-target-normalized
             'mcmc/mh-proposal-normalized
             'mcmc/mh-all-proposals-accepted
             'mcmc/mh-kernel-equals-proposal
             'mcmc/mh-kernel-rows-normalized
             'mcmc/mh-detailed-balance
             'mcmc/mh-target-stationary
             'mcmc/mh-mixes-in-one-step}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))

(deftest executable-two-state-mh-demo-matches-checked-claims
  (let [{:keys [target kernel row-totals balanced-flow-0-1
                balanced-flow-1-0 one-step-from-uniform]}
        (executable/demo)]
    (is (= {0 1/3, 1 2/3} target))
    (is (= {0 {0 1/3, 1 2/3}
            1 {0 1/3, 1 2/3}}
           kernel))
    (is (= {0 1, 1 1} row-totals))
    (is (= balanced-flow-0-1 balanced-flow-1-0))
    (is (= 2/9 balanced-flow-0-1))
    (is (= target one-step-from-uniform))))
