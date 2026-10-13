(ns rainbow.math.finite.bellman-greedy-policy-optimal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-greedy-policy-optimal
             :as optimal]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (optimal/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-bellman-greedy-policy-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (optimal/definition-ids env)
        theorems (optimal/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/nnrat-greedy-bellman-policy-is-admissible
             'value/nnrat-greedy-bellman-policy-value-is-optimal
             'value/nnrat-greedy-bellman-policy-optimal-certificate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
