(ns rainbow.milestones.nnrat-product-reassociation-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nnrat-product-reassociation
             :as milestone]))

(deftest precommitted-product-reassociation-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-proved experiment)))
    (is (= 3 (:candidate-proved experiment)))
    (is (= {:targets 1 :baseline-successes 0
            :candidate-successes 1 :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:targets 1 :baseline-successes 0
            :candidate-successes 1 :success-rate-change 1}
           (:transfer experiment)))
    (is (= 6 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 1/3 (get-in experiment
                        [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 1 (get-in experiment
                      [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :commutative-semigroup-laws
           (get-in report [:capability :algebraic-scope])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (= {:precommit-recorded 1245 :input-checkpoint-actual 1237
            :reason :precommit-copied-current-global-count}
           (get-in report [:source :mapping-count-correction])))
    (is (false? (get-in report
                        [:claim-boundaries :distributivity-proved?])))
    (is (false? (get-in report
                        [:claim-boundaries :cancellation-proved?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1236 (count (:mappings checkpoint))))))
