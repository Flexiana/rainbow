(ns rainbow.history.nat-infinitude-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as day54]
            [rainbow.history.nat-infinitude :as nat-infinitude]))

(deftest nat-infinitude-report-is-content-addressed-and-paired
  (let [result (nat-infinitude/load-report nat-infinitude/report-path)
        report (edn/read-string (slurp nat-infinitude/report-path))]
    (is (= :replayed (:status result)))
    (is (= "sha256:63b5c5447bc8913a7866edbe7eb4019b8db6424000fbd05643647ce433ca6fb7"
           (:report/id result)))
    (is (= {:status :blocked :reason :state-budget :states-created 32}
           (get-in report [:experiment :baseline])))
    (is (= {:status :proved :states-created 2 :reuse-successes 1}
           (get-in report [:experiment :candidate])))
    (is (= {#{} 1} (get-in report [:proofs :new-axiom-profiles])))
    (is (true? (get-in report [:claim-boundaries
                               :development-only-proof-gain?])))))

(deftest nat-infinitude-checkpoint-replays-one-new-mapping
  (let [checkpoint (day54/load-checkpoint nat-infinitude/checkpoint-path)
        mapping (first (filter #(= nat-infinitude/target-name (:foreign/name %))
                               (:mappings checkpoint)))
        source (last (get-in checkpoint [:source
                                         :additional-statement-batches]))]
    (is (= :replayed (:status checkpoint)))
    (is (= "sha256:8cadb6fc3cec4851dc65f31d077a84cf600119860ed4f95e9fb7710e9e44923c"
           (:checkpoint/id checkpoint)))
    (is (= 1183 (count (:mappings checkpoint))))
    (is (= nat-infinitude/target-name (:foreign/name mapping)))
    (is (empty? (:axioms mapping)))
    (is (= :nat-finite-list-bound (:kind source)))
    (is (= :redacted (:proof-values source)))))
