(ns rainbow.algorithms.proofs.ahof.discrete-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.discrete-search :as ds]))

(def checked-environment
  (delay
    (let [c (checkpoint/load-checkpoint
             "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status c))
        (throw (ex-info "D63 checkpoint rejected" {:c c})))
      (ds/extend-environment (:environment c)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                      (set (:rainbow/universes d)))))))

(deftest discrete-search-are-native-axiom-free
  (let [env @checked-environment
        ids (merge (ds/definition-ids env) (ds/theorem-ids env))]
    (is (= #{'dp/knapsack-cell 'plan/rrt-nearest 'sample/star-discrepancy-upper
             'aco/pheromone-update
             'dp/knapsack-at-least-exclude 'dp/knapsack-at-least-include
             'plan/rrt-nearest-below-left 'plan/rrt-nearest-below-right
             'sample/star-discrepancy-bounds-box0 'aco/pheromone-update-example}
           (set (keys ids))))
    (doseq [[nm id] ids]
      (is (checked? env id) (str nm))
      (is (= #{} (kernel/axioms env id)) (str nm)))))
