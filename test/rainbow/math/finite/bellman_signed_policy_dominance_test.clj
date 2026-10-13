(ns rainbow.math.finite.bellman-signed-policy-dominance-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-policy-dominance
             :as dominance]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (dominance/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest signed-policy-dominance-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (dominance/definition-ids env)
        theorems (dominance/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/nnrat-transition-signed-optimality-step-monotone
             'value/signed-abstract-post-fixed-value-below-sequence
             'value/signed-policy-fixed-point-below-optimality-step
             'value/signed-rate-limit-dominates-below-iterates
             'value/signed-convergence-certificate-dominates-below-value
             'value/signed-post-fixed-value-below-operator-iterate
             'value/nnrat-transition-signed-optimality-operator-monotone
             'value/nnrat-transition-signed-policy-fixed-point-below-optimality-operator
             'value/nnrat-transition-signed-policy-value-below-optimality-operator-iterate
             'value/nnrat-transition-signed-policy-value-below-optimality-fixed-point}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
