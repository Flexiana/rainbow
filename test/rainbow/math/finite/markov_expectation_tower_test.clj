(ns rainbow.math.finite.markov-expectation-tower-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-expectation-tower :as tower]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (tower/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-expectation-tower-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (tower/definition-ids env)
        theorems (tower/theorem-ids env)]
    (is (= #{'markov/nnrat-kernel-observable}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-expectation-after-kernel-step
             'markov/nnrat-stationary-kernel-observable-expectation}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
