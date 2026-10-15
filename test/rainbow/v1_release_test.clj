(ns rainbow.v1-release-test
  (:require [clojure.test :refer :all]
            [rainbow.history.release-gate :as v1]))

(def live-report (delay (v1/report)))

(deftest every-v1-release-gate-passes
  (let [report @live-report]
    (is (= :passed (:status report)))
    (is (= #{:A :B :C :D :E :F} (set (keys (:gates report)))))
    (doseq [[gate result] (:gates report)]
      (is (= :passed (:status result)) (str "Gate " gate))
      (is (seq (:evidence result))))))

(deftest both-required-v1-demonstrations-pass
  (is (= {:independent-lean-cross-checked-reproving :passed
          :executable-decision-application :passed}
         (:required-demonstrations @live-report))))

(deftest formerly-missing-v1-capabilities-have-replayable-evidence
  (is (every? true? (vals (:v1-capabilities @live-report))))
  (is (= 11 (get-in @live-report [:replay :content-addressed-reports])))
  (is (= 9 (get-in @live-report [:replay :checked-environments])))
  (is (true? (get-in @live-report [:replay :proof-graph]))))

(deftest compactness-bounds-audited-machinery-not-the-kernel-checked-corpus
  (let [compactness (:compactness @live-report)]
    (is (< (:audited-machinery-lines compactness)
           (:audited-machinery-cap compactness)))
    (is (pos? (:proof-corpus-lines compactness)))
    (is (= :none (:proof-corpus-cap compactness)))
    (is (= 1364 (:trusted-base-lines compactness)))
    (testing "the split is exhaustive, so nothing escapes both buckets"
      (is (= (:production-source-lines compactness)
             (+ (:audited-machinery-lines compactness)
                (:proof-corpus-lines compactness)))))))
