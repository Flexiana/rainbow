(ns rainbow.history.finite-constant-ranges-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finite-constant-ranges :as finite-constant-ranges]))

(def expected-names (set finite-constant-ranges/target-names))

(deftest finite-range-report-is-content-addressed-and-measured
  (let [result (finite-constant-ranges/load-report finite-constant-ranges/report-path)
        report (edn/read-string (slurp finite-constant-ranges/report-path))
        evaluation (first (get-in report [:experiment :evaluations]))]
    (is (= :replayed (:status result)))
    (is (= "sha256:04bf777d8b2583f11eb5e1342df282540eddddf746458cd1ce8974a25b111264"
           (:report/id result)))
    (is (= 0 (get-in report [:experiment :baseline-nativeizable])))
    (is (= 1 (get-in report [:experiment :candidate-nativeizable])))
    (is (= :rejected (:baseline-nativeization/status evaluation)))
    (is (= :mathlib-native/kernel-rejected
           (:baseline-nativeization/error-category evaluation)))
    (is (= :nativeized (:candidate-nativeization/status evaluation)))
    (is (= :proved (:candidate/status evaluation)))
    (is (= 2 (:candidate/states-created evaluation)))
    (is (= 1 (:candidate/reuse-successes evaluation)))
    (is (true? (:design-exposed? evaluation)))
    (is (= :declarative-level-reorder-and-domain-predecessor
           (get-in report [:representation :nativeizer-change])))))

(deftest finite-range-checkpoint-replays-one-axiom-free-mapping
  (let [checkpoint (day54/load-checkpoint finite-constant-ranges/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:8e7941431466d04d762fb21179d980aa91447f1223b8e7f6cf469f26c9495e90"
           (:checkpoint/id checkpoint)))
    (is (= 1219 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 1 (count mappings) (count (set (map :proof/id mappings)))))
    (is (empty? (:axioms (first mappings))))
    (is (= :finite-set-range-bridge (:kind source)))
    (is (= expected-names (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
