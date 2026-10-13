(ns rainbow.milestones.ahof-trust-region-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-trust-region :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o16-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o16 (first (filter #(= "O16" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o16)))
    (is (= (:evidence/id report)
           (get-in o16 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o16-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[decision/reduction-ratio
                   decision/trust-accept
                   decision/trust-region-update
                   decision/trust-region-update-accepts
                   decision/trust-region-update-rejects
                   ahof-o16/accept-decision-is-true
                   ahof-o16/reject-decision-is-false
                   ahof-o16/accepted-step-is-candidate
                   ahof-o16/rejected-step-is-current
                   ahof-o16/trust-region]]
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

(deftest worked-trust-region-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :accept-ratio])))
    (is (= 1/4 (get-in report [:evaluation :clojure-reference :reject-ratio])))
    (is (= 0 (get-in report [:evaluation :clojure-reference :accepted-result])))
    (is (= 2 (get-in report [:evaluation :clojure-reference :rejected-result])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :both-branches-exercised])))
    (is (= :proved (get-in report [:claim-boundaries :accept-reject-branch])))
    (is (= :proved (get-in report [:claim-boundaries :both-branches-exercised])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :region-radius-adjustment])))))
