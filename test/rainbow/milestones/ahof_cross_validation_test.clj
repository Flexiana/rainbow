(ns rainbow.milestones.ahof-cross-validation-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-cross-validation :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest v4-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        v4 (first (filter #(= "V4" (:ahof/id %))
                          (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome v4)))
    (is (= (:evidence/id report)
           (get-in v4 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest v4-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[validation/cross-validation-total
                   validation/cross-validation-mean
                   validation/cross-validation-total-unfold
                   validation/cross-validation-mean-unfold
                   ahof-v4/total-is-one
                   ahof-v4/mean-is-one-half
                   ahof-v4/cross-validation]]
      (let [id (environment/resolve-id checked-environment name)
            declaration (environment/declaration checked-environment id)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (= :checked
               (:status
                (kernel/check checked-environment
                              (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))
            (str name))))))

(deftest worked-cross-validation-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [3/4 1/4] (get-in report [:evaluation :clojure-reference :fold-scores])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :fold-total])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :mean])))
    (is (= :proved (get-in report [:claim-boundaries :fold-averaging])))
    (is (= :proved (get-in report [:claim-boundaries :list-sum-then-division])))
    (is (= :not-claimed (get-in report [:claim-boundaries :model-fitting])))))
