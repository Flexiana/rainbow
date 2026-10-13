(ns rainbow.history.finset-powersets-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finset-powersets :as finset-powersets]))

(def expected-names (set finset-powersets/target-names))

(deftest finset-powerset-report-is-content-addressed-and-measured
  (let [result (finset-powersets/load-report finset-powersets/report-path)
        report (edn/read-string (slurp finset-powersets/report-path))
        evaluations (get-in report [:experiment :evaluations])]
    (is (= :replayed (:status result)))
    (is (= "sha256:6ee6e9df88b3493c8c5efee497d44d5b4f9bc8d39a7464043634340279bfbe3b"
           (:report/id result)))
    (is (= 0 (get-in report [:experiment :baseline-nativeizable])))
    (is (= 2 (get-in report [:experiment :candidate-nativeizable])))
    (is (= 2 (count evaluations)))
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
    (is (= :extensional-finset-powerset
           (get-in report [:representation :method])))))

(deftest finset-powerset-checkpoint-replays-two-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finset-powersets/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:d8b58ad794155b2adccac69e9030189a68514e3ea405264d74286fe096ce1866"
           (:checkpoint/id checkpoint)))
    (is (= 1218 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 2 (count mappings) (count (set (map :proof/id mappings)))))
    (is (= {4 2} (frequencies (map (comp count :axioms) mappings))))
    (is (= :extensional-finset-powerset (:kind source)))
    (is (= expected-names (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
