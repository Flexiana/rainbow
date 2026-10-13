(ns rainbow.milestones.ahof-pattern-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-pattern-search :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o35-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o35 (first (filter #(= "O35" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o35)))
    (is (= (:evidence/id report)
           (get-in o35 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o35-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[search/poll-better
                   search/poll-improves
                   search/pattern-move
                   search/poll-better-unfold
                   search/pattern-move-unfold
                   ahof-o35/poll-picks-backward
                   ahof-o35/move-accepts-best
                   ahof-o35/pattern-search]]
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

(deftest worked-pattern-search-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 9 (get-in report [:evaluation :clojure-reference :forward-objective])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :backward-objective])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :polled-best])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :moved-to])))
    (is (true? (get-in report [:evaluation :clojure-reference :derivative-free])))
    (is (= :proved (get-in report [:claim-boundaries :derivative-free-poll])))
    (is (= :proved (get-in report [:claim-boundaries :argmin-selection])))
    (is (= :not-claimed (get-in report [:claim-boundaries :convergence])))))
