(ns rainbow.math.finite.markov-hastings-flow-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-hastings-flow :as hastings]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (hastings/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest general-hastings-flow-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (hastings/definition-ids env)
        theorems (hastings/theorem-ids env)]
    (is (= #{'mcmc/nnrat-hastings-accepted-flow
             'mcmc/nnrat-hastings-ratio-acceptance
             'mcmc/nnrat-hastings-accepted-transition
             'mcmc/nnrat-hastings-rejection-mass
             'mcmc/nnrat-hastings-completed-kernel
             'mcmc/nnrat-hastings-rejection-correction
             'mcmc/nnrat-off-diagonal-zero
             'mcmc/nnrat-hastings-diagonal-rejection-placement
             'mcmc/nnrat-hastings-canonical-kernel
             'mcmc/nnrat-symmetric-flow
             'mcmc/nnrat-hastings-kernel-realization}
           (set (keys definitions))))
    (is (= #{'nnrat/min-commutative
             'mcmc/nnrat-hastings-accepted-flow-symmetric
             'mcmc/nnrat-positive-hastings-ratio-realizes-accepted-flow
             'mcmc/nnrat-zero-hastings-ratio-realizes-accepted-flow
             'mcmc/nnrat-made-hastings-ratio-realizes-accepted-flow
             'mcmc/nnrat-hastings-ratio-realizes-accepted-flow
             'mcmc/nnrat-positive-hastings-ratio-acceptance-at-most-one
             'mcmc/nnrat-zero-hastings-ratio-acceptance-at-most-one
             'mcmc/nnrat-made-hastings-ratio-acceptance-at-most-one
             'mcmc/nnrat-hastings-ratio-acceptance-at-most-one
             'mcmc/nnrat-hastings-accepted-transition-at-most-proposal
             'mcmc/nnrat-hastings-accepted-transition-realizes-flow
             'mcmc/nnrat-hastings-accepted-row-at-most-proposal-row
             'mcmc/nnrat-hastings-accepted-row-at-most-one
             'mcmc/nnrat-hastings-accepted-row-plus-rejection-is-one
             'mcmc/nnrat-hastings-completed-kernel-rows-normalized
             'mcmc/nnrat-hastings-completed-kernel-realization
             'mcmc/nnrat-hastings-rejection-correction-symmetric-of-off-diagonal-zero
             'mcmc/nnrat-hastings-completed-kernel-detailed-balance
             'mcmc/nnrat-hastings-completed-kernel-stationary
             'mcmc/nnrat-hastings-completed-kernel-stationary-of-off-diagonal-zero
             'mcmc/nnrat-hastings-diagonal-rejection-placement-off-diagonal-zero
             'mcmc/nnrat-hastings-diagonal-rejection-placement-has-rejection-mass
             'mcmc/nnrat-hastings-canonical-kernel-stationary
             'mcmc/nnrat-hastings-canonical-kernel-stationary-of-exhaustive-carrier
             'mcmc/nnrat-hastings-realization-detailed-balance
             'mcmc/nnrat-hastings-realization-stationary}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
