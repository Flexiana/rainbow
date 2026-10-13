(ns rainbow.milestones.ahof-local-search-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-local-search :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d40-report-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d40 (first (filter #(= "D40" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= :proved (:ahof/outcome d40)))
    (is (= (:evidence/id report)
           (get-in d40 [:ahof/evidence 0 :evidence/id])))
    (is (= {:before [0 4] :after [4 4]}
           (get-in report [:results :held-out])))
    (is (= {:after [1 1]} (get-in report [:results :transfer])))
    (is (= 9 (get-in report [:results :newly-solved-native-results])))
    (is (= :none (:trusted-base-delta report)))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest d40-certificates-remain-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[search/nnrat-best-neighbor
                   search/nnrat-hill-climb
                   search/nnrat-best-neighbor-is-candidate
                   search/nnrat-best-neighbor-improves
                   search/nnrat-hill-climb-zero
                   search/nnrat-hill-climb-successor
                   search/nnrat-best-neighbor-transfer
                   ahof-d40/best-is-one
                   ahof-d40/admissible
                   ahof-d40/improvement
                   ahof-d40/hill-climb-recurrence
                   ahof-d40/local-search]]
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

(deftest worked-local-search-keeps-proof-and-execution-claims-distinct
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= :normalized (get-in report [:evaluation :status])))
    (is (= 1 (get-in report [:evaluation :clojure-reference :best-neighbor])))
    (is (= {0 1/4 1 3/4 2 1/2}
           (get-in report [:evaluation :clojure-reference :objective-values])))
    (is (= :proved (get-in report [:claim-boundaries :monotone-improvement])))
    (is (= :tested-structural-observation
           (get-in report [:claim-boundaries :clojure-correspondence])))
    (is (= :not-claimed (get-in report [:claim-boundaries :global-optimum])))))
