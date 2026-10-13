(ns rainbow.milestones.rational-value-iteration-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.rational-value-iteration :as milestone]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def target-names (set (map first milestone/target-support)))

(deftest report-and-checkpoint-replay-the-precommitted-rational-chain
  (let [report (edn/read-string (slurp milestone/report-path))
        report-replay (milestone/load-report milestone/report-path)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (is (= :passed (:status report)))
    (is (= :replayed (:status report-replay)))
    (is (= :replayed (:status checkpoint)))
    (is (= 0 (get-in report
                     [:precommitted-capability-experiment :baseline
                      :native-targets-present])))
    (is (= 12 (get-in report
                      [:precommitted-capability-experiment
                       :candidate-proved])))
    (is (= 4 (get-in report
                     [:precommitted-capability-experiment :held-out
                      :candidate-successes])))
    (is (= 2 (get-in report
                     [:precommitted-capability-experiment :transfer
                      :candidate-successes])))
    (is (= target-names
           (set (map :target/name
                     (get-in report
                             [:precommitted-capability-experiment
                              :evaluations])))))
    (is (= :semantics-preserving-definitional-equality-reflexivity-fast-path
           (get-in report [:capability :trusted-base-delta :kind])))
    (is (false? (get-in report
                        [:capability :trusted-base-delta
                         :acceptance-rule-change?])))
    (is (every? :cross-products-match?
                (get-in report
                        [:executable-example :rainbow-evaluation :outputs])))
    (is (= 1237 (get-in report [:proofs :exact-mathlib-mappings-total])))
    (is (= 1237 (get-in report [:checkpoint :mappings])))
    (doseq [name target-names]
      (let [id (environment/resolve-id checked-environment name)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))))))
