(ns rainbow.math.finite.bellman-residual-certificate-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-residual-certificate
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

(deftest finite-bellman-residual-certificate-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (certificate/definition-ids env)
        theorems (certificate/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'nnrat/additive-upper-triangle
             'value/nnrat-optimality-fixed-point-sup-radius-self-bound
             'value/nnrat-optimality-fixed-point-residual-bound
             'value/nnrat-optimality-fixed-point-stopping-certificate}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
