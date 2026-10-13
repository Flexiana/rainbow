(ns rainbow.math.finite.policy-iteration-optimal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.policy-iteration-optimal
             :as policy-iteration-optimal]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (policy-iteration-optimal/extend-environment
       (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest stationary-policy-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (policy-iteration-optimal/definition-ids env)
                   (policy-iteration-optimal/theorem-ids env))]
    (is (= #{'value/nnrat-stationary-policy-satisfies-optimality-equation
             'value/nnrat-stationary-policy-value-is-optimal-given-uniqueness}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
