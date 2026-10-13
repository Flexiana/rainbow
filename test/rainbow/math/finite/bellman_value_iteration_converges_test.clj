(ns rainbow.math.finite.bellman-value-iteration-converges-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-value-iteration-converges :as convergence]))

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
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest bellman-value-iteration-convergence-results-are-axiom-free
  (let [env @checked-environment
        ids (merge (convergence/definition-ids env)
                   (convergence/theorem-ids env))]
    (is (= #{'value/nnrat-vi-error-radius
             'value/nnrat-function-additive-upper-transport
             'value/nnrat-function-additive-lower-transport
             'value/nnrat-optimality-step-fixed-point-contraction
             'value/nnrat-optimality-fixed-point-additive-advance
             'value/nnrat-iterate-successor-additive-upper
             'value/nnrat-iterate-successor-additive-lower
             'value/nnrat-iterate-successor-additively-close
             'value/nnrat-iterate-zero-additively-close
             'value/nnrat-iterate-fixed-point-additive-radius
             'analysis/nnrat-vi-error-radius-rate-null
             'value/nnrat-optimality-iterate-fixed-point-converges
             'analysis/nnrat-at-most-of-rate-null-upper-bounds
             'value/nnrat-bellman-fixed-point-dominates-post-fixed-value
             'value/nnrat-policy-fixed-point-below-optimality-step
             'value/nnrat-policy-value-below-bellman-fixed-point}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
