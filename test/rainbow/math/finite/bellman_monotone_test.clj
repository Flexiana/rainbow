(ns rainbow.math.finite.bellman-monotone-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-monotone :as monotone]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (monotone/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-bellman-monotonicity-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (monotone/definition-ids env)
                   (monotone/theorem-ids env))]
    (is (= #{'list/nnrat-map-sum-monotone
             'probability/nnrat-expectation-monotone
             'bellman/nnrat-action-backup-monotone
             'value/nnrat-optimality-step-monotone}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
