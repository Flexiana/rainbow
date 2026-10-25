(ns rainbow.history.finite-powersets-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.finite-powersets :as finite-powersets]))

(def expected-names (set finite-powersets/target-names))

(deftest finite-powerset-report-is-content-addressed-and-paired
  (let [result (finite-powersets/load-report finite-powersets/report-path)
        report (edn/read-string (slurp finite-powersets/report-path))
        evaluations (get-in report [:experiment :evaluations])
        by-name (into {} (map (juxt :foreign/name identity)) evaluations)]
    (is (= :replayed (:status result)))
    (is (= "sha256:91b1d15a8970201c873ec25bcad112d79b64c0a2623667e68dcd5e570f75f57a"
           (:report/id result)))
    (is (= {:baseline/status :blocked
            :baseline/reason :frontier-exhausted
            :baseline/states-created 12
            :candidate/status :proved
            :candidate/states-created 2
            :candidate/reuse-successes 1}
           (select-keys
            (get by-name "Equiv.finsetSubtypeComm._proof_1")
            [:baseline/status :baseline/reason :baseline/states-created
             :candidate/status :candidate/states-created
             :candidate/reuse-successes])))
    (doseq [name ["Set.Infinite.sUnion" "Set.Finite.powerset"]]
      (is (= :state-budget (get-in by-name [name :baseline/reason])))
      (is (= 32 (get-in by-name [name :baseline/states-created])))
      (is (= :proved (get-in by-name [name :candidate/status])))
      (is (= 2 (get-in by-name [name :candidate/states-created]))))
    (is (false? (get-in report [:experiment :partition-integrity
                                :held-out-result-used-as-validation?])))
    (is (= 0 (get-in report [:experiment :partition-integrity
                             :valid-held-out-or-transfer-gain])))))

(deftest finite-powerset-checkpoint-replays-three-new-mappings
  (let [checkpoint (day54/load-checkpoint finite-powersets/checkpoint-path)
        mappings (filterv #(contains? expected-names (:foreign/name %))
                          (:mappings checkpoint))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:907f5b533090a3a1a87b3a637b984c7b545d52e66cf17a25b49029ae62687272"
           (:checkpoint/id checkpoint)))
    (is (= 1189 (count (:mappings checkpoint))))
    (is (= expected-names (set (map :foreign/name mappings))))
    (is (= 3 (count (set (map :proof/id mappings)))))
    (is (= #{1 3} (set (map (comp count :axioms) mappings))))
    (is (= :finite-powerset-foundation (:kind source)))
    (is (= finite-powersets/design-exposed-targets
           (:design-exposed-targets source)))
    (is (= :redacted (:proof-values source)))))
