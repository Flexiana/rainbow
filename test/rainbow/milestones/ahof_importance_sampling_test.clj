(ns rainbow.milestones.ahof-importance-sampling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-importance-sampling :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d7-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d7 (first (filter #(= "D7" (:ahof/id %))
                          (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d7)))
    (is (= (:evidence/id report)
           (get-in d7 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d7-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[estimation/weighted-sum
                   estimation/total-weight
                   estimation/importance-estimate
                   estimation/importance-estimate-unfold
                   ahof-d7/weighted-sum-is-three
                   ahof-d7/total-weight-is-four
                   ahof-d7/estimate-is-three-quarters
                   ahof-d7/importance-sampling]]
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

(deftest worked-importance-sampling-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 3 (get-in report [:evaluation :clojure-reference :weighted-sum])))
    (is (= 4 (get-in report [:evaluation :clojure-reference :total-weight])))
    (is (= 3/4 (get-in report [:evaluation :clojure-reference :estimate])))
    (is (true? (get-in report [:evaluation :clojure-reference
                               :normalization-nontrivial])))
    (is (= :proved (get-in report [:claim-boundaries :importance-weighting])))
    (is (= :proved
           (get-in report [:claim-boundaries :handles-unnormalized-weights])))
    (is (= :not-claimed (get-in report [:claim-boundaries :variance-reduction])))))
