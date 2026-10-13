(ns rainbow.math.finite.bellman-signed-optimality-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-optimality :as optimality]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (optimality/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-signed-bellman-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (optimality/definition-ids env)
        theorems (optimality/theorem-ids env)]
    (is (= #{'value/signed-greedy-action
             'value/signed-optimality-step}
           (set (keys definitions))))
    (is (= #{'value/signed-greedy-action-is-admissible
             'value/signed-optimality-step-dominates
             'value/signed-optimality-step-unfold
             'value/signed-optimality-step-dominates-policy
             'value/signed-optimality-step-additive-upper-bound
             'value/signed-optimality-step-additively-nonexpansive}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
