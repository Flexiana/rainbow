(ns rainbow.milestones.ahof-robustness-objective-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-robustness-objective :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest v13-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        v13 (first (filter #(= "V13" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome v13)))
    (is (= (:evidence/id report)
           (get-in v13 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest v13-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[validation/falsification-objective
                   validation/falsification-objective-unfold
                   validation/falsification-objective-involution
                   ahof-v13/satisfying-objective-is-negative-two
                   ahof-v13/violating-objective-is-one
                   ahof-v13/robustness-objective]]
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

(deftest worked-robustness-objective-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= -2 (get-in report [:evaluation :clojure-reference :satisfying-objective])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :violating-objective])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :maximizing-favours-violation])))
    (is (= :proved (get-in report [:claim-boundaries :sign-flip-semantics])))
    (is (= :proved (get-in report [:claim-boundaries :objective-involution])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :stl-robustness-evaluator])))))
