(ns rainbow.milestones.ahof-exact-inference-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-exact-inference :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d2-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d2 (first (filter #(= "D2" (:ahof/id %))
                          (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d2)))
    (is (= (:evidence/id report)
           (get-in d2 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d2-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[inference/nnrat-joint
                   inference/nnrat-marginal
                   inference/nnrat-joint-unfold
                   inference/nnrat-marginal-unfold
                   inference/nnrat-marginal-is-enumerated-joint
                   inference/nnrat-marginal-transfer
                   ahof-d2/marginal-values
                   ahof-d2/normalization
                   ahof-d2/exact-inference]]
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

(deftest worked-inference-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (every? :matches? (get-in report [:evaluation :rainbow :values])))
    (is (= {:b1 3/4 :b0 1/4}
           (get-in report [:evaluation :clojure-reference :marginals])))
    (is (= :proved (get-in report [:claim-boundaries :marginal-normalization])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :multi-variable-elimination])))))
