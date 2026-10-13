(ns rainbow.milestones.finite-nat-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.finite-nat :as milestone]))

(deftest precommitted-finite-nat-cluster-is-complete-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 8 (get-in report [:proofs :new-foreign-mappings])))
    (is (= 8 (get-in report [:equal-resource-experiment
                              :search-cost :proved-targets])))
    (is (= 16 (get-in report [:equal-resource-experiment
                               :search-cost :total-states])))
    (is (= [] (get-in report [:equal-resource-experiment
                               :remaining-failures])))
    (is (true? (get-in report [:claim-boundaries
                                :canonical-cardinality-complete-for-computational-finset?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1227 (count (:mappings checkpoint))))))
