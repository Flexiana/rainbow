(ns rainbow.math.finite.bellman-signed-transition-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-signed-transition-bridge
             :as bridge]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (bridge/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-bellman-signed-transition-bridge-is-native-and-axiom-free
  (let [env @checked-environment
        definitions (bridge/definition-ids env)
        theorems (bridge/theorem-ids env)]
    (is (empty? definitions))
    (is (= #{'signed/map-sum-from-nnrat
             'probability/signed-total-mass-from-nnrat
             'probability/signed-embedded-mass-nonnegative
             'probability/signed-total-mass-normalized-from-nnrat
             'value/nnrat-transition-signed-optimality-step-additively-contractive}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
