(ns rainbow.milestones.finite-metric-separation-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.finite-metric-separation :as milestone]))

(deftest precommitted-finite-metric-separation-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status
                      (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 6 (:candidate-proved experiment)))
    (is (= {:targets 2
            :baseline-successes 0
            :candidate-successes 2
            :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:targets 1 :candidate-successes 1}
           (:transfer experiment)))
    (is (= 12 (get-in experiment
                      [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/3
           (get-in experiment
                   [:lemma-leverage
                    :held-out-targets-per-new-theorem])))
    (is (= 1
           (get-in experiment
                   [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (true? (get-in report
                       [:claim-boundaries
                        :native-targets-not-counted-as-mathlib-mappings?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :function-equality-outside-support-claimed?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :complete-metric-fixed-point-claimed?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1245 (count (:mappings checkpoint))))))
