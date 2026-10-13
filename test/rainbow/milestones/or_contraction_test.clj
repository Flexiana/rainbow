(ns rainbow.milestones.or-contraction-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.or-contraction :as milestone]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def target-names
  (set (map first milestone/target-support)))

(deftest report-and-checkpoint-replay-with-all-precommitted-targets
  (let [report (edn/read-string (slurp milestone/report-path))
        report-replay (milestone/load-report milestone/report-path)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (is (= :passed (:status report)))
    (is (= :replayed (:status report-replay)))
    (is (= :replayed (:status checkpoint)))
    (is (= 9 (get-in report
                     [:equal-resource-experiment :candidate-proved])))
    (is (= 0 (get-in report
                     [:equal-resource-experiment :baseline-proved])))
    (is (= 3 (get-in report
                     [:equal-resource-experiment :held-out
                      :candidate-successes])))
    (is (= 2 (get-in report
                     [:equal-resource-experiment :transfer
                      :candidate-successes])))
    (is (= target-names
           (set (map :target/name
                     (get-in report
                             [:equal-resource-experiment :evaluations])))))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (true? (get-in report
                       [:executable-example :rainbow-evaluation
                        :matches-expected-distance?])))
    (doseq [name target-names]
      (let [id (environment/resolve-id checked-environment name)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))))))
