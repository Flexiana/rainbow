(ns rainbow.milestones.nnrat-additive-reassociation-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nnrat-additive-reassociation :as milestone]))

(deftest precommitted-additive-reassociation-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 3 (:candidate-proved experiment)))
    (is (= {:targets 1
            :baseline-successes 0
            :candidate-successes 1
            :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:targets 1
            :baseline-successes 0
            :candidate-successes 1
            :success-rate-change 1}
           (:transfer experiment)))
    (is (= 6 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/3
           (get-in experiment
                   [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 1
           (get-in experiment
                   [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :kernel-checked-nat-semiring-proof-terms
           (get-in report [:capability :normalization])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (false?
         (get-in report
                 [:claim-boundaries :additive-cancellation-proved?])))
    (is (false?
         (get-in report
                 [:claim-boundaries :signed-addition-congruence-proved?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1237 (count (:mappings checkpoint))))))
