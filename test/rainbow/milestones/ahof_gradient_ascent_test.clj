(ns rainbow.milestones.ahof-gradient-ascent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-gradient-ascent :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d49-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d49 (first (filter #(= "D49" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d49)))
    (is (= (:evidence/id report)
           (get-in d49 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d49-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/nnrat-ascent-step
                   optimization/nnrat-ascent-iterate
                   optimization/nnrat-ascent-step-unfold
                   optimization/nnrat-ascent-iterate-zero
                   optimization/nnrat-ascent-iterate-successor
                   optimization/nnrat-ascent-step-transfer
                   ahof-d49/gradient-ascent-recurrence
                   ahof-d49/worked-trajectory
                   ahof-d49/gradient-ascent]]
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

(deftest worked-gradient-ascent-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (every? :matches? (get-in report [:evaluation :rainbow :values])))
    (is (= [0 1/2 1 3/2]
           (get-in report [:evaluation :clojure-reference :trajectory])))
    (is (= :proved (get-in report [:claim-boundaries :worked-exact-trajectory])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :convergence-to-optimum])))))
