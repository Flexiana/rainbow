(ns rainbow.math.finite.markov-kernel-composition-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-kernel-composition :as composition]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (composition/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-kernel-composition-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (composition/definition-ids env)
        theorems (composition/theorem-ids env)]
    (is (= #{'markov/nnrat-kernel-compose}
           (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-step-preserves-total-mass-equivalence
             'markov/nnrat-kernel-step-preserves-normalization
             'markov/nnrat-kernel-step-compose
             'markov/nnrat-kernel-compose-rows-normalized
             'markov/nnrat-common-stationary-under-kernel-compose}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
