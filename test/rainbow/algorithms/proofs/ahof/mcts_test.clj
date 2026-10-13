(ns rainbow.algorithms.proofs.ahof.mcts-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.mcts :as mcts]
            [rainbow.algorithms.reference.mcts :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mcts/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest mcts-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mcts/definition-ids checked-environment)
        theorems (mcts/theorem-ids checked-environment)]
    (is (= #{'mcts/ucb-score 'mcts/tree-policy-value}
           (set (keys definitions))))
    (is (= #{'mcts/ucb-score-example 'mcts/selects-max-ucb
             'mcts/dominates-first 'mcts/dominates-third}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-mcts-selects-max-ucb
  (is (= 5 (executable/ucb-score 3 2)))
  (is (= 7 (executable/tree-policy-value [5 7 4])))
  (is (= 1 (executable/select-child [5 7 4]))))
