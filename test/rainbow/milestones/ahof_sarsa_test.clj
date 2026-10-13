(ns rainbow.milestones.ahof-sarsa-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-sarsa :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d62-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d62 (first (filter #(= "D62" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d62)))
    (is (= (:evidence/id report)
           (get-in d62 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d62-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[learning/signed-sarsa-update
                   learning/signed-sarsa-update-unfold
                   learning/signed-sarsa-equals-q-update
                   ahof-d62/updated-is-one-half
                   ahof-d62/coincides-with-q-update
                   ahof-d62/sarsa]]
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

(deftest worked-sarsa-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :td-error])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :updated])))
    (is (= :proved (get-in report [:claim-boundaries :on-policy-td-update])))
    (is (= :proved
           (get-in report [:claim-boundaries
                           :coincides-with-q-learning-on-bootstrap])))
    (is (= :not-claimed (get-in report [:claim-boundaries :convergence])))))
