(ns rainbow.history.infinitude-transport-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.infinitude-transport :as infinitude-transport]))

(def expected-names #{"Int.infinite" "Infinite.of_surjective"})

(deftest infinite-transport-report-is-content-addressed-and-honest
  (let [result (infinitude-transport/load-report infinitude-transport/report-path)
        report (edn/read-string (slurp infinitude-transport/report-path))
        evaluations (get-in report [:experiment :evaluations])
        by-name (into {} (map (juxt :foreign/name identity)) evaluations)]
    (is (= :replayed (:status result)))
    (is (= "sha256:7424621cb61ef8a88535d651e90a48e32ac47ee8f84849333c83d6e68b737b25"
           (:report/id result)))
    (is (= :rejected
           (get-in by-name ["Int.infinite"
                            :baseline-nativeization/status])))
    (is (= :proved (get-in by-name ["Int.infinite" :candidate/status])))
    (is (= :proved
           (get-in by-name ["Infinite.of_surjective" :candidate/status])))
    (is (= :blocked
           (get-in by-name ["Infinite.of_injective" :candidate/status])))
    (is (true? (get-in by-name ["Infinite.of_surjective"
                                :design-exposed?])))
    (is (false? (get-in report [:experiment :partition-integrity
                                :transfer-result-used-as-promotion-evidence?])))
    (is (= 0 (get-in report [:experiment :partition-integrity
                             :valid-held-out-or-transfer-gain])))))

(deftest infinite-transport-checkpoint-replays-two-axiom-free-mappings
  (let [checkpoint (day54/load-checkpoint infinitude-transport/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:a3c10ad34472dc4e7a511c595df02cace339263a293008163b234610d7b4e7eb"
           (:checkpoint/id checkpoint)))
    (is (= 1186 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 2 (count (set (map :proof/id mappings)))))
    (is (every? (comp empty? :axioms) mappings))
    (is (= :sort-polymorphic-infinite-transport (:kind source)))
    (is (= infinitude-transport/design-exposed-targets (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
