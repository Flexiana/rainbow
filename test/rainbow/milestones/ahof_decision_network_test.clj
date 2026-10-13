(ns rainbow.milestones.ahof-decision-network-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-decision-network :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d18-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d18 (first (filter #(= "D18" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d18)))
    (is (= (:evidence/id report)
           (get-in d18 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d18-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[decision/network-value
                   decision/network-value-unfold
                   ahof-d18/network-eu-is-three-quarters
                   ahof-d18/utility-at-zero-is-one
                   ahof-d18/utility-at-one-is-zero
                   ahof-d18/decision-network]]
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

(deftest worked-decision-network-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3/4 (get-in report [:evaluation :clojure-reference :expected-utility])))
    (is (= {0 3/4 1 1/4}
           (get-in report [:evaluation :clojure-reference :probabilities])))
    (is (= :proved
           (get-in report [:claim-boundaries :expected-utility-evaluation])))
    (is (= :proved (get-in report [:claim-boundaries :finite-inference-engine])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :decision-node-optimization])))))
