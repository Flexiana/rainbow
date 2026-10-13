(ns rainbow.math.finite.markov-ergodic-hypotheses-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-ergodic-hypotheses
             :as hypotheses]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (hypotheses/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-hastings-ergodic-hypotheses-are-native-and-axiom-free
  (let [env @checked-environment
        definitions (hypotheses/definition-ids env)
        theorems (hypotheses/theorem-ids env)]
    (is (= #{'markov/nnrat-ergodic-hypotheses}
           (set (keys definitions))))
    (is (= #{'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized
             'mcmc/nnrat-hastings-index-ergodic-hypotheses-of-full-support
             'mcmc/nnrat-hastings-index-stationary-and-ergodic-hypotheses-of-full-support}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
