(ns rainbow.math.finite.bellman-signed-value-iteration-converges-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-value-iteration-converges
             :as convergence]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (convergence/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-bellman-signed-value-iteration-convergence-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (convergence/definition-ids env)
        theorems (convergence/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/signed-vi-error-radius-is-nnrat-power-scale
             'analysis/signed-vi-error-radius-rate-null-of-at-most-half
             'value/nnrat-transition-signed-iterate-fixed-point-converges-at-most-half}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
