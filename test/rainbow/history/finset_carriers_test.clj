(ns rainbow.history.finset-carriers-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finset-carriers :as finset-carriers]))

(def expected-names (set finset-carriers/target-names))

(deftest fintype-report-is-content-addressed-and-measured
  (let [result (finset-carriers/load-report finset-carriers/report-path)
        report (edn/read-string (slurp finset-carriers/report-path))
        evaluations (get-in report [:experiment :evaluations])]
    (is (= :replayed (:status result)))
    (is (= "sha256:30f800eb32672db98b1e8291ed76e8bc3a2b81a183a15a5d820ba693c8ad0c68"
           (:report/id result)))
    (is (= 0 (get-in report [:experiment :baseline-nativeizable])))
    (is (= 9 (get-in report [:experiment :candidate-nativeizable])))
    (is (= 9 (count evaluations)))
    (is (every? #(= :rejected (:baseline-nativeization/status %))
                evaluations))
    (is (every? #(= :mathlib-native/unknown-constant
                    (:baseline-nativeization/error-category %))
                evaluations))
    (is (every? #(= :nativeized (:candidate-nativeization/status %))
                evaluations))
    (is (every? #(= :proved (:candidate/status %)) evaluations))
    (is (every? #(= 2 (:candidate/states-created %)) evaluations))
    (is (every? #(= 1 (:candidate/reuse-successes %)) evaluations))
    (is (every? :design-exposed? evaluations))
    (is (false? (get-in report [:experiment :partition-integrity
                                :held-out-result-used-as-validation?])))
    (is (= 0 (get-in report [:experiment :partition-integrity
                             :valid-held-out-or-transfer-gain])))
    (is (= :extensional-complete-finset
           (get-in report [:representation :method])))
    (is (= :subtype-of-finset-with-total-membership
           (get-in report [:representation :native-shape])))))

(deftest fintype-checkpoint-replays-nine-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finset-carriers/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:e26301146b7f4cbe3e4dd67098abeeef2388d9208796814ac3ebcae55dcfd574"
           (:checkpoint/id checkpoint)))
    (is (= 1212 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 9 (count mappings) (count (set (map :proof/id mappings)))))
    (is (= {0 5, 1 1, 2 2, 3 1}
           (frequencies (map (comp count :axioms) mappings))))
    (is (= :extensional-complete-fintype (:kind source)))
    (is (= expected-names (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
