(ns rainbow.math.finite.bellman-value-optimality-theorem-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-value-optimality-theorem
             :as optimality-theorem]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (optimality-theorem/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest abstract-bellman-value-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (optimality-theorem/definition-ids env)
                   (optimality-theorem/theorem-ids env))]
    (is (= #{'value/nnrat-abstract-value-iteration-converges
             'value/nnrat-rate-limit-dominates-below-iterates
             'value/nnrat-abstract-post-fixed-value-below-sequence
             'value/nnrat-abstract-bellman-policy-optimality}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
