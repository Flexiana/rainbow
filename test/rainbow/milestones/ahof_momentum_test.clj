(ns rainbow.milestones.ahof-momentum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-momentum :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o19-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o19 (first (filter #(= "O19" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o19)))
    (is (= (:evidence/id report)
           (get-in o19 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o19-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/momentum-velocity
                   optimization/momentum-step
                   optimization/momentum-iterate
                   optimization/momentum-velocity-unfold
                   optimization/momentum-step-unfold
                   optimization/momentum-iterate-zero
                   optimization/momentum-iterate-successor
                   ahof-o19/first-velocity-is-one
                   ahof-o19/first-position-is-one
                   ahof-o19/momentum]]
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

(deftest worked-momentum-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [1 1] (get-in report [:evaluation :clojure-reference :first-step])))
    (is (= 2 (get-in report [:evaluation :clojure-reference :momentum-carry])))
    (is (= :proved (get-in report [:claim-boundaries :momentum-carry])))
    (is (= :proved (get-in report [:claim-boundaries :pair-valued-state])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :convergence-rate])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :acceleration-theorem])))))
