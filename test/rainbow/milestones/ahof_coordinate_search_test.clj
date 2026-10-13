(ns rainbow.milestones.ahof-coordinate-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-coordinate-search :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o32-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o32 (first (filter #(= "O32" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o32)))
    (is (= (:evidence/id report)
           (get-in o32 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o32-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[search/coordinate-update-first
                   search/coordinate-update-second
                   search/coordinate-cycle
                   search/coordinate-iterate
                   search/coordinate-cycle-unfold
                   search/coordinate-iterate-zero
                   ahof-o32/first-coordinate-descends-to-zero
                   ahof-o32/second-coordinate-descends-to-zero
                   ahof-o32/coordinate-recurrence
                   ahof-o32/coordinate-search]]
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

(deftest worked-coordinate-search-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= [0 2]
           (get-in report [:evaluation :clojure-reference
                           :after-first-coordinate])))
    (is (= [0 0]
           (get-in report [:evaluation :clojure-reference :after-cycle])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :second-update-sees-first])))
    (is (= :proved
           (get-in report [:claim-boundaries :coordinatewise-composition])))
    (is (= :proved
           (get-in report [:claim-boundaries :sequential-coordinate-dependence])))
    (is (= :not-claimed (get-in report [:claim-boundaries :convergence])))))
