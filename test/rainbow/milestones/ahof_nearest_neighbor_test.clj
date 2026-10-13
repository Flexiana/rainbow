(ns rainbow.milestones.ahof-nearest-neighbor-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-nearest-neighbor :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d25-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d25 (first (filter #(= "D25" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d25)))
    (is (= (:evidence/id report)
           (get-in d25 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d25-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[decision/nearest-value
                   decision/nearest-value-unfold
                   ahof-d25/query-near-a-is-value-a
                   ahof-d25/query-near-b-is-value-b
                   ahof-d25/nearest-neighbor]]
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

(deftest worked-nearest-neighbor-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3/4 (get-in report [:evaluation :clojure-reference :query-near-a])))
    (is (= 1/4 (get-in report [:evaluation :clojure-reference :query-near-b])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :follows-nearer-point])))
    (is (= :proved
           (get-in report [:claim-boundaries :nonparametric-value-lookup])))
    (is (= :proved (get-in report [:claim-boundaries :follows-nearer-point])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :k-nearest-averaging])))))
