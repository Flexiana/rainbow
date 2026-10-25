(ns rainbow.milestones.nat-distance-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.milestones.nat-distance :as milestone]))

(deftest precommitted-natural-distance-cluster-is-measured-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))
        experiment (:equal-resource-experiment report)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 0 (:baseline-nativeizable experiment)))
    (is (= 10 (:candidate-nativeizable experiment)))
    (is (= 10 (:candidate-proved experiment)))
    (is (= {:baseline-successes 0 :targets 2
            :candidate-successes 2 :success-rate-change 1}
           (:held-out experiment)))
    (is (= {:baseline-successes 0 :targets 2 :candidate-successes 2}
           (:transfer experiment)))
    (is (= 26 (get-in experiment [:search-cost :total-states])))
    (is (= [] (:remaining-failures experiment)))
    (is (= {#{} 10} (get-in report [:proofs :new-axiom-profiles])))
    (is (= :none (get-in report [:capability :trusted-base-delta])))
    (is (true? (get-in report [:claim-boundaries
                                :triangle-inequality-proved?])))
    (is (true? (get-in report [:claim-boundaries
                                :linear-order-representation-complete?])))
    (is (= :replayed (:status checkpoint)))
    (is (= 1236 (count (:mappings checkpoint))))))
