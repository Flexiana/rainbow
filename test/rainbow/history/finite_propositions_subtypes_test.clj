(ns rainbow.history.finite-propositions-subtypes-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finite-propositions-subtypes :as finite-propositions-subtypes])
  (:import (java.io PushbackReader)
           (java.util.zip GZIPInputStream)))

;; The stored checkpoint as written, read here rather than through day54's private reader so
;; the test needs only day54's public functions.
(defn- stored-checkpoint [path]
  (with-open [reader (PushbackReader. (io/reader (GZIPInputStream. (io/input-stream path))))]
    (edn/read reader)))

;; instFiniteProp was retracted in 1.4.2: its reproof used large elimination from a
;; proposition with several constructors, which the kernel now refuses.
(def expected-names
  #{"Set.Finite.eq_1" "Finite.of_subsingleton"})

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

(deftest finite-subtype-checkpoint-replays-two-mappings-and-records-the-retraction
  (let [checkpoint (day54/load-checkpoint finite-propositions-subtypes/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:767502a478c68c333c1659c92fc4f7150b92415e075ef21f49a3e70758b2dbe7"
           (:checkpoint/id checkpoint)))
    (is (= 1182 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 2 (count (set (map :proof/id mappings)))))
    (is (= ["instFiniteProp"]
           (mapv :foreign/name (:retracted-mappings (stored-checkpoint finite-propositions-subtypes/checkpoint-path)))))
    (is (= :finite-subtype-boundary (:kind source)))
    (is (= :redacted (:proof-values source)))))
