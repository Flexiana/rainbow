(ns rainbow.milestones.ahof-network-scoring-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-network-scoring :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d14-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d14 (first (filter #(= "D14" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d14)))
    (is (= (:evidence/id report)
           (get-in d14 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 2] :after [2 2]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 5 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d14-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[scoring/nnrat-total-score
                   scoring/score-empty
                   scoring/score-cons
                   ahof-d14/score-is-one
                   ahof-d14/network-scoring]]
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

(deftest worked-scoring-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :total-score])))
    (is (= {0 1/2 1 1/4 2 1/4}
           (get-in report [:evaluation :clojure-reference :local-scores])))
    (is (= :proved (get-in report [:claim-boundaries :additive-decomposition])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :bic-bdeu-formula])))))
