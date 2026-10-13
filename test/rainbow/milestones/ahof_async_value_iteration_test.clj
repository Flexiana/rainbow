(ns rainbow.milestones.ahof-async-value-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-async-value-iteration :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.reference.async-value-iteration :as executable]
            [rainbow.algorithms.reference.value-iteration :as sync]))

(deftest d23-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d23 (first (filter #(= "D23" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d23)))
    (is (= (:evidence/id report)
           (get-in d23 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 7] :after [7 7]}
           (get-in report [:results :held-out])))
    (is (= {:after [2 2]} (get-in report [:results :transfer])))
    (is (= 13 (get-in report [:results :newly-solved-native-results])))
    (is (= 1237 (get-in report [:checkpoint :exact-mathlib-mappings])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d23-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[value/nnrat-async-update
                   value/nnrat-async-iterate
                   value/nnrat-async-update-selected
                   value/nnrat-async-update-preserved
                   value/nnrat-async-iterate-zero
                   value/nnrat-async-iterate-successor
                   value/nnrat-async-update-selected-dominates
                   value/nnrat-async-state-schedule-transfer
                   ahof-d23/schedule-selects-zero
                   ahof-d23/schedule-skips-one
                   ahof-d23/selected-update
                   ahof-d23/preserved-update
                   ahof-d23/async-recurrence
                   ahof-d23/greedy-actions
                   ahof-d23/two-step-async-values
                   ahof-d23/async-value-iteration]]
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

(deftest worked-async-iteration-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (every? :matches?
                (get-in report [:evaluation :rainbow :values])))
    (is (= {0 0, 1 0}
           (get-in report [:evaluation :clojure-reference :values])))
    (is (= :proved
           (get-in report [:claim-boundaries :selected-state-update])))
    (is (= :proved
           (get-in report [:claim-boundaries :non-selected-preservation])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report
                   [:claim-boundaries :infinite-limit-convergence])))))

(deftest executable-async-selection-shapes-the-trajectory
  ;; The pluggable schedule is what distinguishes asynchronous from synchronous
  ;; iteration: refreshing only a subset of states leaves the others behind.
  (let [model {:states [0 1] :actions [0 1]
               :transition (fn [_ a n] (if (= a n) 1 0))
               :reward (fn [_ a] (if (= a 1) 2 1))
               :discount 1/2 :fallback (constantly 0)}
        only-zero (fn [_step] #(= % 0))]
    (is (= {0 3N, 1 3N} (sync/value-iterate model 2 {0 0, 1 0})))
    (is (= {0 2N, 1 0} (executable/async-iterate model only-zero 2 {0 0, 1 0})))))
