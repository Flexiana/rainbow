(ns rainbow.math.finite.greedy-optimal-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.greedy-optimal :as greedy-optimal]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (greedy-optimal/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [declaration (environment/declaration env id)]
    (= :checked
       (:status
        (kernel/check env
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest greedy-policy-optimality-is-native-and-axiom-free
  (let [env @checked-environment
        ids (merge (greedy-optimal/definition-ids env)
                   (greedy-optimal/theorem-ids env))]
    (is (= #{'value/nnrat-greedy-policy-fixes-optimal-value
             'value/nnrat-greedy-bellman-policy-fixes-optimal-value
             'value/nnrat-greedy-policy-value-is-optimal-given-uniqueness}
           (set (keys ids))))
    (doseq [[name id] ids]
      (is (checked? env id) (str name))
      (is (= #{} (kernel/axioms env id)) (str name)))))
