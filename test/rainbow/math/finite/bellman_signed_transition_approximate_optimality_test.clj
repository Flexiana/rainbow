(ns rainbow.math.finite.bellman-signed-transition-approximate-optimality-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-transition-approximate-optimality
             :as laws]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (laws/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest normalized-transition-approximate-optimality-is-axiom-free
  (let [env @checked-environment]
    (testing "constructive pointwise and finite-sup residual certificates"
      (is (empty? (laws/definition-ids env)))
      (is (= #{'value/nnrat-transition-signed-optimality-successive-iterate-additive-radius
               'value/nnrat-transition-signed-optimality-approximate-fixed-point-general-rate
               'value/nnrat-transition-signed-optimality-approximate-fixed-point-exists-general-rate
               'value/nnrat-transition-signed-optimality-approximate-fixed-point-sup-general-rate}
             (set (keys (laws/theorem-ids env)))))
      (doseq [[name id] (laws/theorem-ids env)]
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
