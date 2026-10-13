(ns rainbow.milestones.ahof-maximum-likelihood-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-maximum-likelihood :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d10-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d10 (first (filter #(= "D10" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d10)))
    (is (= (:evidence/id report)
           (get-in d10 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d10-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[estimation/log-likelihood-total
                   estimation/mle-prefers
                   estimation/log-likelihood-total-unfold
                   estimation/mle-prefers-unfold
                   ahof-d10/model-a-total-is-three-halves
                   ahof-d10/model-b-total-is-one-half
                   ahof-d10/mle-prefers-model-a
                   ahof-d10/maximum-likelihood]]
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

(deftest worked-maximum-likelihood-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3/2 (get-in report [:evaluation :clojure-reference :model-a-total])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :model-b-total])))
    (is (= :model-a (get-in report [:evaluation :clojure-reference :estimate])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :prefers-higher-likelihood])))
    (is (= :proved
           (get-in report [:claim-boundaries :summed-log-likelihood-objective])))
    (is (= :proved
           (get-in report [:claim-boundaries :model-preference-by-comparison])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :gradient-based-fitting])))))
