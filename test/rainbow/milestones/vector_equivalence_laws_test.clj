(ns rainbow.milestones.vector-equivalence-laws-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.vector-equivalence-laws :as milestone]))

(deftest precommitted-vector-equivalence-laws-are-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 4 (:candidate-proved experiment)))
    (is (= {:targets 2
            :baseline-successes 0
            :candidate-successes 2
            :success-rate-change 2}
           (:held-out experiment)))
    (is (= 8 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/2
           (get-in experiment
                   [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 1
           (get-in experiment
                   [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :finite-lists-of-grothendieck-pair-signed-rationals
           (get-in report [:capability :representation])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (false?
         (get-in report
                 [:claim-boundaries
                  :vector-equivalence-transitivity-proved?])))
    (is (false?
         (get-in report
                 [:claim-boundaries :vector-addition-congruence-proved?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1236 (count (:mappings checkpoint))))))
