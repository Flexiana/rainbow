(ns rainbow.math.finite.bellman-signed-value-iteration-general-converges-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-value-iteration-general-converges
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

(deftest finite-bellman-general-signed-convergence-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (convergence/definition-ids env)
        theorems (convergence/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'analysis/signed-rate-null-from-nnrat
             'analysis/signed-general-harmonic-rate-null
             'signed/nnrat-power-scale-general-harmonic-bound
             'analysis/signed-nnrat-power-rate-null-general
             'analysis/signed-vi-error-radius-rate-null-general
             'value/nnrat-transition-signed-iterate-fixed-point-converges-general-rate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
