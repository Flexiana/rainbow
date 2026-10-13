(ns rainbow.algorithms.proofs.decision-guarantee-audit-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.decision-guarantee-audit :as audit]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/or-rational-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "Rational OR checkpoint rejected"
                        {:checkpoint checkpoint})))
      (audit/extend-environment (:environment checkpoint)))))

(defn- kernel-checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Audit test expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- evaluates-to? [checked-environment expression expected]
  (let [normalized
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    (and (= :normalized (:status normalized))
         (= (core checked-environment expected) (:term normalized)))))

(deftest two-required-theorems-and-instance-certificates-are-kernel-checked
  (let [checked-environment @checked-environment
        ids (audit/theorem-ids checked-environment)]
    (is (string? (audit/block-id checked-environment)))
    (is (every? string? (vals (audit/definition-ids checked-environment))))
    (doseq [name '[audit/decision-guarantee-sound audit/refusal-path
                   audit-ex-1/all-losses-at-most-ten
                   audit-ex-1/audit-approved
                   audit-ex-2/refused-missing-cap
                   audit-ex-3/refused-cap-exceeds-bound
                   audit-ex-4/refused-missing-support]]
      (let [id (get ids name)]
        (is (string? id) (str name))
        (is (kernel-checked? checked-environment id) (str name))
        (is (= #{} (kernel/axioms checked-environment id)) (str name))))))

(deftest required-audit-results-normalize-to-the-declared-outcomes
  (let [checked-environment @checked-environment]
    (is (evaluates-to? checked-environment
                       [:const 'audit-ex-1/result []]
                       [:const 'audit/approved []]))
    (is (evaluates-to? checked-environment
                       [:const 'audit-ex-2/result []]
                       [:const 'audit/missing-cap []]))
    (is (evaluates-to? checked-environment
                       [:const 'audit-ex-3/result []]
                       [:const 'audit/cap-exceeds-bound []]))
    (is (evaluates-to? checked-environment
                       [:const 'audit-ex-4/result []]
                       [:const 'audit/missing-support []]))))

(deftest worked-losses-are-exactly-ten-four-and-zero
  (let [checked-environment @checked-environment
        numerator [:const 'nnrat/numerator []]
        loss [:const 'audit-ex/loss []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        numeral (fn [n] (nth (iterate #(vector :app successor %) zero) n))]
    (doseq [[action expected] [[zero 10] [one 4] [two 0]]]
      (is (evaluates-to?
           checked-environment
           [:app numerator [:app loss action]]
           (numeral expected))))))
