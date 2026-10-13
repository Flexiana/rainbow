(ns rainbow.milestones.strict-contraction-stabilization-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.strict-contraction-stabilization
             :as milestone]))

(deftest precommitted-stabilization-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 8 (:candidate-proved experiment)))
    (is (= {:targets 2 :baseline-successes 0
            :candidate-successes 2 :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:targets 1 :candidate-successes 1} (:transfer experiment)))
    (is (= 16 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 2/9 (get-in experiment
                        [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 8/9 (get-in experiment
                        [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :initial-consecutive-finite-sup-distance
           (get-in report [:capability :iteration-bound])))
    (is (= :declared-finite-support
           (get-in report [:capability :fixed-point-scope])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (true? (get-in report
                       [:claim-boundaries
                        :existence-by-bounded-stabilization-proved?])))
    (is (true? (get-in report
                       [:claim-boundaries
                        :fixed-point-only-on-declared-support?])))
    (is (false? (get-in report
                        [:claim-boundaries :bellman-specialization-proved?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1245 (count (:mappings checkpoint))))))
