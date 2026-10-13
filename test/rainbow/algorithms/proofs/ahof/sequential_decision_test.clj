(ns rainbow.algorithms.proofs.ahof.sequential-decision-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.sequential-decision :as sd]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (sd/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest sequential-decision-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (sd/definition-ids env) (sd/theorem-ids env))]
    (is (= #{'game/best-response-value 'rl/rmax-value 'rl/sweep-priority
             'rl/model-based-value 'rl/replay-target
             'game/best-response-dominates 'rl/rmax-optimistic 'rl/sweep-picks-max-priority
             'rl/model-based-example 'rl/replay-target-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
