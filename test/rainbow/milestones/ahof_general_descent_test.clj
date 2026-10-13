(ns rainbow.milestones.ahof-general-descent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-general-descent :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o13-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o13 (first (filter #(= "O13" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o13)))
    (is (= (:evidence/id report)
           (get-in o13 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o13-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/general-descent-step
                   optimization/general-descent-iterate
                   optimization/general-descent-step-unfold
                   optimization/general-descent-iterate-zero
                   optimization/general-descent-iterate-successor
                   ahof-o13/trajectory
                   ahof-o13/trajectory-values
                   ahof-o13/descent-recurrence
                   ahof-o13/general-descent]]
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

(deftest worked-general-descent-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [1 1/2 0 -1/2]
           (get-in report [:evaluation :clojure-reference :trajectory])))
    (is (= :gradient-descent
           (get-in report [:evaluation :clojure-reference :instance])))
    (is (= :proved
           (get-in report [:claim-boundaries :three-pluggable-functions])))
    (is (= :proved
           (get-in report [:claim-boundaries :gradient-descent-instance])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed (get-in report [:claim-boundaries :convergence])))))
