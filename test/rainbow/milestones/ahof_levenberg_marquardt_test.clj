(ns rainbow.milestones.ahof-levenberg-marquardt-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-levenberg-marquardt :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o31-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o31 (first (filter #(= "O31" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o31)))
    (is (= (:evidence/id report)
           (get-in o31 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o31-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[optimization/levenberg-marquardt-rate
                   optimization/levenberg-marquardt-rate-unfold
                   nnrat/reciprocal
                   ahof-o31/step-size
                   ahof-o31/damped-step-is-one
                   ahof-o31/levenberg-marquardt-recurrence
                   ahof-o31/levenberg-marquardt]]
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

(deftest worked-lm-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1/4 (get-in report [:evaluation :clojure-reference :lm-rate])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :lm-first-step])))
    (is (= 0 (get-in report [:evaluation :clojure-reference :newton-first-step])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :damping-shortens-step])))
    (is (= :proved
           (get-in report [:claim-boundaries :damped-hessian-inverse-step])))
    (is (= :proved (get-in report [:claim-boundaries :rational-division-used])))
    (is (= :not-claimed (get-in report [:claim-boundaries :adaptive-damping])))))
