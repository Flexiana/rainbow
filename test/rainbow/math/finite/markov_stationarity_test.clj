(ns rainbow.math.finite.markov-stationarity-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-stationarity :as stationarity]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (stationarity/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-stationarity-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (stationarity/definition-ids env)
        theorems (stationarity/theorem-ids env)]
    (is (= #{'markov/nnrat-kernel-step
             'markov/nnrat-kernel-rows-normalized
             'markov/nnrat-detailed-balance
             'markov/nnrat-stationary}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-step-respects-mass-equivalence
             'markov/nnrat-kernel-step-respects-kernel-equivalence
             'markov/nnrat-kernel-step-respects-equivalence
             'markov/nnrat-detailed-balance-implies-stationary
             'markov/nnrat-stationary-step-normalized}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
