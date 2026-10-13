(ns rainbow.history.finset-extensional-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finset-extensional :as finset-extensional]))

(def expected-names (set finset-extensional/target-names))

(deftest finset-report-is-content-addressed-and-measured
  (let [result (finset-extensional/load-report finset-extensional/report-path)
        report (edn/read-string (slurp finset-extensional/report-path))
        evaluations (get-in report [:experiment :evaluations])]
    (is (= :replayed (:status result)))
    (is (= "sha256:35759f3ba62304b6293498e4ee89db6251bf259bb182e480d3feca5d6da19d39"
           (:report/id result)))
    (is (= 0 (get-in report [:experiment :baseline-nativeizable])))
    (is (= 13 (get-in report [:experiment :candidate-nativeizable])))
    (is (= 13 (count evaluations)))
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
    (is (= :extensional-bundled-finite-predicate
           (get-in report [:representation :method])))
    (is (= :subtype-of-set-with-list-cover
           (get-in report [:representation :native-shape])))
    (is (= :multiset-quotient
           (get-in report [:representation :foreign-shape])))))

(deftest finset-checkpoint-replays-thirteen-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finset-extensional/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:3c4b259001f33f8468c09c427bcd45c633fd2ae9c1f8c83473159b59b872ed8f"
           (:checkpoint/id checkpoint)))
    (is (= 1203 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 13 (count mappings) (count (set (map :proof/id mappings)))))
    (is (= {0 9, 1 1, 4 3}
           (frequencies (map (comp count :axioms) mappings))))
    (is (= :extensional-bundled-finset (:kind source)))
    (is (= expected-names (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
