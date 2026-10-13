(ns rainbow.milestones.ahof-stl-robustness-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-stl-robustness :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest v6-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        v6 (first (filter #(= "V6" (:ahof/id %))
                          (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome v6)))
    (is (= (:evidence/id report)
           (get-in v6 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 3] :after [3 3]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 8 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest v6-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[validation/signed-decide-at-most
                   validation/signed-min
                   validation/signed-max
                   validation/signed-min-preserved
                   validation/signed-max-preserved
                   ahof-v6/and-selects-minimum
                   ahof-v6/robustness-values
                   ahof-v6/stl-robustness]]
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

(deftest worked-robustness-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= -1/4 (get-in report [:evaluation :clojure-reference
                                :and-robustness])))
    (is (= 1/2 (get-in report [:evaluation :clojure-reference :or-robustness])))
    (is (false? (get-in report [:evaluation :clojure-reference :and-satisfied])))
    (is (= :proved (get-in report [:claim-boundaries :conjunction-is-minimum])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed
           (get-in report [:claim-boundaries :temporal-until-operator])))))
