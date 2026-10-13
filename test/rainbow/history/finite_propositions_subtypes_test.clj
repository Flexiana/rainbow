(ns rainbow.history.finite-propositions-subtypes-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finite-propositions-subtypes :as finite-propositions-subtypes]))

(def expected-names
  #{"instFiniteProp" "Set.Finite.eq_1" "Finite.of_subsingleton"})

(deftest finite-subtype-report-is-content-addressed-and-held-out-validated
  (let [result (finite-propositions-subtypes/load-report finite-propositions-subtypes/report-path)
        report (edn/read-string (slurp finite-propositions-subtypes/report-path))]
    (is (= :replayed (:status result)))
    (is (= "sha256:376952009c7caf0465d050e9de9b74905cc54df0e5639aa2288bdf0f87a0db32"
           (:report/id result)))
    (is (= :normalize-to-implicit
           (get-in report [:nativeization :instance-implicit-policy])))
    (is (= 2 (get-in report [:experiment :development-targets])))
    (is (= 1 (get-in report [:experiment :held-out-targets])))
    (is (every? #(= :proved (:candidate/status %))
                (get-in report [:experiment :evaluations])))
    (is (every? #(= 2 (:candidate/states-created %))
                (get-in report [:experiment :evaluations])))))

(deftest finite-subtype-checkpoint-replays-three-distinct-mappings
  (let [checkpoint (day54/load-checkpoint finite-propositions-subtypes/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:22037603f6faaf9feb38993f65078576698de916fbf73532c3d4bd10080c325f"
           (:checkpoint/id checkpoint)))
    (is (= 1183 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 3 (count (set (map :proof/id mappings)))))
    (is (= :finite-subtype-boundary (:kind source)))
    (is (= :redacted (:proof-values source)))))
