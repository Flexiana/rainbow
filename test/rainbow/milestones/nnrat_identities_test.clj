(ns rainbow.milestones.nnrat-identities-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nnrat-identities :as milestone]))

(deftest precommitted-identities-are-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 2 (:baseline-proved experiment)))
    (is (= 8 (:candidate-proved experiment)))
    (is (= {:targets 1 :baseline-successes 1
            :candidate-successes 1 :success-rate-change 0}
           (:held-out experiment)))
    (is (= {:targets 1 :baseline-successes 0
            :candidate-successes 1 :success-rate-change 1}
           (:transfer experiment)))
    (is (= 16 (get-in experiment [:search-cost :candidate :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= 0 (get-in experiment
                      [:lemma-leverage :held-out-targets-per-new-theorem])))
    (is (= 3/4 (get-in experiment
                        [:lemma-leverage :all-targets-per-new-theorem])))
    (is (= :native-numerator-positive-denominator-pairs
           (get-in report [:capability :representation])))
    (is (= :cross-product-equivalence
           (get-in report [:capability :equality])))
    (is (= #{'nnrat/add-commutative 'nnrat/multiply-commutative}
           (get-in report
                   [:source :dependency-minimization
                    :precommitted-but-not-required])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (false? (get-in report
                        [:claim-boundaries :field-structure-claimed?])))
    (is (false? (get-in report
                        [:claim-boundaries :division-by-zero-law-claimed?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1244 (count (:mappings checkpoint))))))
