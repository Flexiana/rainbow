(ns rainbow.history.finset-nontrivial-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finset-nontrivial :as finset-nontrivial]))

(def expected-names (set finset-nontrivial/target-names))

(deftest finset-nontrivial-report-is-content-addressed-and-measured
  (let [result (finset-nontrivial/load-report finset-nontrivial/report-path)
        report (edn/read-string (slurp finset-nontrivial/report-path))
        evaluations (get-in report [:experiment :evaluations])]
    (is (= :replayed (:status result)))
    (is (= "sha256:66311dbebd47cb9e84becf97c651eacae00cee7bb9151dfd64888508118482b8"
           (:report/id result)))
    (is (= 0 (get-in report [:experiment :baseline-nativeizable])))
    (is (= 4 (get-in report [:experiment :candidate-nativeizable])))
    (is (= 4 (count evaluations)))
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
    (is (= :finset-set-nontrivial-view
           (get-in report [:representation :method])))))

(deftest finset-nontrivial-checkpoint-replays-four-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finset-nontrivial/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:c2164d551e837cabd30d975b099d012a741d04111c653127fd6100bada69ca32"
           (:checkpoint/id checkpoint)))
    (is (= 1215 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 4 (count mappings) (count (set (map :proof/id mappings)))))
    (is (= {0 3, 1 1}
           (frequencies (map (comp count :axioms) mappings))))
    (is (= :finset-set-nontrivial-bridge (:kind source)))
    (is (= expected-names (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
