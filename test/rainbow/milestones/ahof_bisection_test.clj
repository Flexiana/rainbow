(ns rainbow.milestones.ahof-bisection-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-bisection :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest o12-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        o12 (first (filter #(= "O12" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome o12)))
    (is (= (:evidence/id report)
           (get-in o12 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest o12-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[search/bracket-midpoint
                   search/bisection-narrow
                   search/bracket-midpoint-unfold
                   search/narrow-keeps-lower
                   search/narrow-keeps-upper
                   ahof-o12/first-midpoint-is-half
                   ahof-o12/narrows-to-lower-half
                   ahof-o12/second-midpoint-is-quarter
                   ahof-o12/bisection]]
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

(deftest worked-bisection-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :first-midpoint])))
    (is (= [0 1/2]
           (get-in report [:evaluation :clojure-reference :lower-bracket])))
    (is (= 1/4
           (get-in report [:evaluation :clojure-reference :second-midpoint])))
    (is (= :proved (get-in report [:claim-boundaries :bracket-halving])))
    (is (= :proved (get-in report [:claim-boundaries :half-selection])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :root-existence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :convergence-limit])))))
