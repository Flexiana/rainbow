(ns rainbow.history.or-curriculum-first-mapping-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.history.or-curriculum-first-mapping :as or-curriculum-first-mapping]))

(deftest first-or-foundation-report-is-content-addressed
  (let [result (or-curriculum-first-mapping/load-report or-curriculum-first-mapping/report-path)]
    (is (= :replayed (:status result)))
    (is (= "sha256:2d578ba5d17e5c4c51f5f6263558da73d1aade5f8f83a5ae4abcf55ad04e7675"
           (:report/id result)))))

(deftest first-or-foundation-checkpoint-replays-with-new-mapping-source
  (let [checkpoint (checkpoint/load-checkpoint or-curriculum-first-mapping/checkpoint-path)
        mapping (first (filter #(= or-curriculum-first-mapping/target-name (:foreign/name %))
                               (:mappings checkpoint)))]
    (is (= :replayed (:status checkpoint)))
    (is (= 1175 (count (:mappings checkpoint))))
    (is (some? mapping))
    (is (= #{} (:axioms mapping)))
    (is (= :operations-research-foundation
           (get-in checkpoint [:source :additional-statement-batches 0
                               :kind])))))
