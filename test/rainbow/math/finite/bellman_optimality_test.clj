(ns rainbow.math.finite.bellman-optimality-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman-optimality :as opt]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d21-policy-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D21 checkpoint rejected" {:checkpoint checkpoint})))
      (opt/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest optimality-step-dominates-policy-is-native-axiom-free
  (let [env @checked-environment
        ids (merge (opt/definition-ids env) (opt/theorem-ids env))]
    (is (= #{'value/nnrat-optimality-step-dominates-policy
             'value/nnrat-greedy-dominates-policy}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
