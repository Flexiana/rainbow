(ns rainbow.milestones.ahof-maximum-expected-utility-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.milestones.ahof-maximum-expected-utility :as milestone]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(deftest d17-report-checkpoint-and-catalog-credit-replay
  (let [loaded (milestone/load-report milestone/report-path)
        report (:report loaded)
        checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        ledger (:ledger (ahof/load-ledger ahof/ledger-path))
        d17 (first (filter #(= "D17" (:ahof/id %))
                           (:ahof-ledger/algorithms ledger)))]
    (is (= :replayed (:status loaded)))
    (is (= :passed (:status report)))
    (is (= :replayed (:status checkpoint)))
    (is (= 1237 (get-in report [:checkpoint :exact-mathlib-mappings])))
    (is (= :proved (:ahof/outcome d17)))
    (is (nil? (:ahof/pending-reason d17)))
    (is (false? (:ahof/shared-foundations-counted-as-algorithm? d17)))
    (is (= (:evidence/id report)
           (get-in d17 [:ahof/evidence 0 :evidence/id])))))

(deftest precommitted-held-out-and-transfer-targets-were-all-unlocked
  (let [report (:report (milestone/load-report milestone/report-path))
        targets (:targets report)]
    (is (= 12 (count targets)))
    (is (every? #(= :missing-representation (:baseline/status %)) targets))
    (is (every? #(= :proved (:candidate/status %)) targets))
    (is (= {:before [0 5] :after [5 5]}
           (get-in report [:results :held-out])))
    (is (= {:after [2 2]} (get-in report [:results :transfer])))
    (is (= {:median 0 :total 0
            :interpretation :installed-kernel-checked-certificates}
           (get-in report [:results :search-states])))
    (is (every? empty? (vals (:axiom-profiles report))))))

(deftest maximum-expected-utility-certificate-remains-kernel-checked
  (let [checkpoint (checkpoint/load-checkpoint milestone/checkpoint-path)
        checked-environment (:environment checkpoint)]
    (doseq [name '[ahof-d17/probabilities-normalized
                   ahof-d17/expected-utility-is-finite-expectation
                   ahof-d17/selected-is-renegotiate
                   ahof-d17/selected-is-member
                   ahof-d17/selected-dominates
                   ahof-d17/maximum-expected-utility]]
      (let [id (environment/resolve-id checked-environment name)
            declaration (environment/declaration checked-environment id)]
        (is (string? id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))
        (is (= :checked
               (:status
                (kernel/check checked-environment
                              (:rainbow/value declaration)
                              (:rainbow/type declaration)
                              (set (:rainbow/universes declaration)))))
            (str name))))))

(deftest executable-claim-boundaries-stay-explicit
  (let [report (:report (milestone/load-report milestone/report-path))]
    (is (= {:mathematical-theorem :proved
            :rainbow-evaluation :computed
            :clojure-correspondence :not-claimed
            :output-satisfies-theorem :proved}
           (:claim-boundaries report)))
    (is (= :renegotiate (get-in report [:evaluation :selected-action])))
    (is (= :normalized (get-in report [:evaluation :status])))))
