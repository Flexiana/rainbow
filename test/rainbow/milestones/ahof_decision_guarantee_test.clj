(ns rainbow.milestones.ahof-decision-guarantee-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-decision-guarantee :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest content-addressed-packet-checkpoint-and-ledger-credit-replay
  (let [loaded (milestone/load-evidence milestone/evidence-path)
        packet (:evidence loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger-result (ahof/load-ledger ahof/ledger-path)
        credit (first (get-in ledger-result
                              [:ledger :ahof-ledger/credited-results]))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status packet)))
    (is (= :replayed (:status checkpoint)))
    (is (= 1237 (get-in packet [:checkpoint :exact-mathlib-mappings])))
    (is (= "decision-guarantee-audit-v0" (:ahof/id credit)))
    (is (= :proved (:ahof/outcome credit)))
    (is (false? (:ahof/shared-finset-foundations-counted-as-algorithm?
                 credit)))
    (is (= (:evidence/id packet)
           (get-in credit [:ahof/evidence 0 :evidence/id])))))

(deftest instances-have-the-required-proof-or-refusal-evidence
  (let [packet (:evidence (milestone/load-evidence milestone/evidence-path))
        instances (into {} (map (juxt :instance/id identity))
                        (:instances packet))]
    (is (= :proved (get-in instances [:audit-ex-1 :result :status])))
    (is (string? (get-in instances [:audit-ex-1 :result :proof-id])))
    (is (= [:refused :missing-cap]
           ((juxt :status :reason) (get-in instances
                                           [:audit-ex-2 :result]))))
    (is (= [:refused :cap-exceeds-bound]
           ((juxt :status :reason) (get-in instances
                                           [:audit-ex-3 :result]))))
    (is (= [:refused :missing-support]
           ((juxt :status :reason) (get-in instances
                                           [:audit-ex-4 :result]))))
    (is (every? #(string? (get-in % [:result :proof-id]))
                (vals instances)))
    (is (every? :matches? (:evaluations packet)))))

(deftest required-theorems-remain-axiom-free-in-the-replayed-environment
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[audit/decision-guarantee-sound audit/refusal-path
                   audit-ex-1/all-losses-at-most-ten]]
      (let [id (environment/resolve-id checked-environment name)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))))))
