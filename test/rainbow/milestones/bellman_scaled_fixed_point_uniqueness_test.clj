(ns rainbow.milestones.bellman-scaled-fixed-point-uniqueness-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.milestones.bellman-scaled-fixed-point-uniqueness
             :as milestone]
            [rainbow.checkpoint :as checkpoint]))

(deftest precommitted-bellman-scaled-uniqueness-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status
                      (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 10 (:candidate-proved experiment)))
    (is (= {:targets 2
            :baseline-successes 0
            :candidate-successes 2
            :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:targets 1 :candidate-successes 1}
           (:transfer experiment)))
    (is (= 20 (get-in experiment
                      [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/5
           (get-in experiment
                   [:lemma-leverage
                    :held-out-targets-per-new-theorem])))
    (is (= 1
           (get-in experiment
                   [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :scale
           (get-in report [:capability :input-value-denominator])))
    (is (= :scale-cubed
           (get-in report [:capability :bellman-output-denominator])))
    (is (= :bellman-value-equals-scale-squared-value
           (get-in report [:capability :fixed-point-equation])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :unscaled-raw-fixed-point-claimed?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :fixed-point-existence-proved?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :value-iteration-convergence-proved?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :function-equality-outside-support-claimed?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1244 (count (:mappings checkpoint))))))
