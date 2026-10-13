(ns rainbow.math.finite.bellman-policy-residual-certificate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-policy-residual-certificate
             :as certificate]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (certificate/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest finite-bellman-policy-residual-certificate-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (certificate/definition-ids env)
        theorems (certificate/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'metric/finite-nnrat-sup-radius-self-bound-of-contracted-image
             'bellman/nnrat-policy-step-fixed-point-contraction
             'bellman/nnrat-policy-fixed-point-sup-radius-self-bound
             'bellman/nnrat-policy-fixed-point-residual-bound
             'bellman/nnrat-policy-fixed-point-stopping-certificate
             'bellman/nnrat-policy-fixed-point-residual-radius-zero
             'bellman/nnrat-policy-fixed-points-have-zero-sup-radius
             'bellman/nnrat-policy-fixed-points-unique}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
