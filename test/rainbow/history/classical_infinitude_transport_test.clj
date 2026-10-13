(ns rainbow.history.classical-infinitude-transport-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.classical-infinitude-transport :as classical-infinitude-transport]))

(deftest infinite-injection-report-is-content-addressed-and-paired
  (let [result (classical-infinitude-transport/load-report classical-infinitude-transport/report-path)
        report (edn/read-string (slurp classical-infinitude-transport/report-path))]
    (is (= :replayed (:status result)))
    (is (= "sha256:61d5b1043ce5d8a8280b94b0ae5f0e7e52ebc8aa09d31f65882d54fde3390087"
           (:report/id result)))
    (is (= {:status :blocked :reason :state-budget :states-created 32}
           (get-in report [:experiment :baseline])))
    (is (= {:status :proved :states-created 2 :reuse-successes 1}
           (get-in report [:experiment :candidate])))
    (is (= 1 (count (get-in report [:proofs :new-axiom-profiles]))))
    (is (= :development (get-in report [:experiment :study/partition])))
    (is (true? (get-in report [:claim-boundaries
                               :development-only-proof-gain?])))))

(deftest infinite-injection-checkpoint-replays-one-classical-mapping
  (let [checkpoint (day54/load-checkpoint classical-infinitude-transport/checkpoint-path)
        mapping (first (filter #(= classical-infinitude-transport/target-name (:foreign/name %))
                               (:mappings checkpoint)))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:3c8bc85a8a6e2fb1e7c0960c6e1f3ab7e73522e1c1e4df8d0a1742ea04704e08"
           (:checkpoint/id checkpoint)))
    (is (= 1187 (count (:mappings checkpoint))))
    (is (= classical-infinitude-transport/target-name (:foreign/name mapping)))
    (is (= 1 (count (:axioms mapping))))
    (is (= :classical-infinite-injection (:kind source)))
    (is (= :redacted (:proof-values source)))))
