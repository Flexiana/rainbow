(ns rainbow.milestones.finite-bellman-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.milestones.finite-bellman :as milestone]))

(deftest precommitted-bellman-chain-is-complete-and-replayable
  (let [report (edn/read-string (slurp milestone/report-path))]
    (is (= :replayed (:status (milestone/load-report milestone/report-path))))
    (is (= :passed (:status report)))
    (is (= 6 (get-in report [:experiment :targets])))
    (is (= 6 (get-in report [:experiment :candidate-proved])))
    (is (= {:proved 2 :targets 2}
           (get-in report [:experiment :held-out])))
    (is (= {:proved 1 :targets 1}
           (get-in report [:experiment :transfer])))
    (is (= #{} (get-in report [:capability :axiom-profile])))
    (is (true? (get-in report [:claim-boundaries
                                :mathematical-theorems-proved?])))
    (is (true? (get-in report [:claim-boundaries
                                :rainbow-evaluator-computed-example?])))
    (is (false? (get-in report [:claim-boundaries
                                 :clojure-implementation-correspondence-proved?])))
    (is (true? (get-in report [:claim-boundaries
                                :computed-output-satisfies-rainbow-theorem?])))))
