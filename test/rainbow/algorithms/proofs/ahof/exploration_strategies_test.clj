(ns rainbow.algorithms.proofs.ahof.exploration-strategies-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.exploration-strategies :as es]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (es/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest exploration-strategies-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (es/definition-ids env) (es/theorem-ids env))]
    (is (= #{'explore/epsilon-greedy 'explore/greedy-value 'explore/explore-then-commit
             'explore/quantile-score 'explore/quantile-select 'explore/softmax-probability
             'explore/epsilon-greedy-exploits 'explore/epsilon-greedy-explores
             'explore/greedy-dominates-left 'explore/greedy-dominates-right
             'explore/explore-then-commit-commits 'explore/explore-then-commit-explores
             'explore/quantile-optimism-example 'explore/softmax-probability-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
