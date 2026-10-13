(ns rainbow.math.finite.bellman-signed-fixed-point-uniqueness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-fixed-point-uniqueness
             :as uniqueness]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (uniqueness/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)
        result (kernel/check env
                             (:rainbow/value declaration)
                             (:rainbow/type declaration)
                             (set (:rainbow/universes declaration)))]
    (= :checked (:status result))))

(deftest signed-bellman-fixed-point-uniqueness-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (uniqueness/definition-ids env)
        theorems (uniqueness/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'value/nnrat-transition-signed-optimality-fixed-points-unique}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
