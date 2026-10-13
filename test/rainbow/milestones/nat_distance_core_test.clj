(ns rainbow.milestones.nat-distance-core-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance-core :as milestone]))

(deftest precommitted-distance-core-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status
                      (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 3 (:baseline-proved experiment)))
    (is (= 7 (:candidate-proved experiment)))
    (is (= {:targets 2
            :baseline-successes 0
            :candidate-successes 2
            :success-rate-change 1}
           (:held-out experiment)))
    (is (= 2 (get-in experiment [:search-cost :median-states])))
    (is (= 22 (get-in experiment [:search-cost :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 5 (get-in experiment
                     [:lemma-leverage :new-generalized-lemmas])))
    (is (= 2/5
           (get-in experiment
                   [:lemma-leverage
                    :held-out-targets-per-generalized-theorem])))
    (is (= {#{} 7} (get-in report [:proofs :new-axiom-profiles])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (true? (get-in report
                       [:claim-boundaries :proof-redacted-evaluation?])))
    (is (false? (get-in report
                        [:claim-boundaries :lean-proof-bodies-imported?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1244 (count (:mappings checkpoint))))))
