(ns rainbow.milestones.signed-equivalence-laws-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.signed-equivalence-laws :as milestone]))

(deftest precommitted-signed-equivalence-laws-are-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 2 (:candidate-proved experiment)))
    (is (= {:targets 1 :baseline-successes 0
            :candidate-successes 1 :success-rate-change 1}
           (:held-out experiment)))
    (is (= 4 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/2 (get-in experiment
                        [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 1 (get-in experiment
                      [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :grothendieck-pairs-of-nonnegative-rationals
           (get-in report [:capability :representation])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (false? (get-in report
                        [:claim-boundaries :transitivity-proved?])))
    (is (false? (get-in report
                        [:claim-boundaries
                         :signed-addition-congruence-proved?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1237 (count (:mappings checkpoint))))))
