(ns rainbow.failure-memory-test
  (:require [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.history.failure-memory :as failure-memory]
            [rainbow.elaborate :as elaborate]
            [rainbow.proof :as proof]
            [rainbow.search :as search]))

(deftest persisted-failures-eliminate-exact-cross-run-retries
  (let [report (failure-memory/report)]
    (is (= :passed (:status report)))
    (is (= 10 (:known-failures report)))
    (is (= 10 (get-in report [:baseline :failed-attempts])))
    (is (= 0 (get-in report [:cached :failed-attempts])))
    (is (= 10 (get-in report [:cached :cache-hits])))
    (is (= 1 (get-in report [:cached :remaining])))
    (is (< (get-in report [:cached :attempts])
           (get-in report [:baseline :attempts])))))

(deftest alpha-equivalent-surface-names-share-a-goal-hash
  (let [environment (direct-term-corpus/build-environment)
        first-target failure-memory/target
        second-target (:term (elaborate/type-expression
                              (first-tactic-program/forall '[X Y] [:-> 'X 'Y])))
        first-state (:state (proof/start environment first-target))
        second-state (:state (proof/start environment second-target))]
    (is (= first-target second-target))
    (is (= (search/goal-hash environment (proof/current-goal first-state))
           (search/goal-hash environment (proof/current-goal second-state))))))

(deftest compressed-blocker-reconstructs-a-valid-unresolved-frontier
  (let [environment (direct-term-corpus/build-environment)
        keys (search/failure-keys (:attempts (failure-memory/stored-blocked-run)))
        result (failure-memory/search-once keys)
        remaining (first (:remaining result))
        reconstructed (proof/start environment (:target remaining)
                                   {:context (:context remaining)})]
    (is (= :blocked (:status result)))
    (is (map? remaining))
    (is (= :ready (:status reconstructed)))
    (is (= (:target remaining)
           (get-in reconstructed [:state :proof/goals 0 :goal/target])))))
