(ns rainbow.math.finite.bellman-signed-policy-optimal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-policy-optimal
             :as policy-optimal]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (policy-optimal/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest signed-policy-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (policy-optimal/definition-ids env)
        theorems (policy-optimal/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/nnrat-transition-signed-policy-step-additively-contractive
             'value/nnrat-transition-signed-policy-fixed-point-sup-distance-self-bound
             'value/nnrat-transition-signed-policy-fixed-point-residual-bound
             'value/nnrat-transition-signed-policy-fixed-point-stopping-certificate
             'value/nnrat-transition-signed-policy-fixed-points-unique
             'value/nnrat-transition-signed-greedy-policy-value-is-optimal
             'value/nnrat-transition-signed-greedy-policy-optimal-certificate
             'value/nnrat-transition-signed-stationary-policy-value-is-optimal}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
