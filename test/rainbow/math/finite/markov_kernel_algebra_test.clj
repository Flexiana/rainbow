(ns rainbow.math.finite.markov-kernel-algebra-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-kernel-algebra :as algebra]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (algebra/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-markov-kernel-algebra-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (algebra/definition-ids env)
        theorems (algebra/theorem-ids env)]
    (is (= #{} (set (keys definitions))))
    (is (= #{'markov/nnrat-kernel-compose-respects-first-equivalence
             'markov/nnrat-kernel-compose-respects-second-equivalence
             'markov/nnrat-kernel-compose-respects-equivalence
             'markov/nnrat-kernel-compose-associative
             'markov/nnrat-kernel-observable-compose}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
