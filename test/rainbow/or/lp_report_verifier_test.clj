(ns rainbow.or.lp-report-verifier-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.lp-report-bridge :as producer]
            [rainbow.or.lp-report-verifier :as verifier]))

(def ^:private instance
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [1 1]
   :plan [1/2 1/2] :prices [1 1]})
(def ^:private report {:achieved 1 :bound 2 :gap 1 :direction :upper})
(def ^:private proofs
  (delay (into {} (map (fn [[k spec]] [k (:value spec)]))
               (:specs (producer/report-specs instance report)))))
(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (producer/extend-environment (:environment r)))))

(deftest actual-proof-values-replay-without-calling-the-producer
  (let [e @env p @proofs
        r (with-redefs [producer/report-specs (fn [& _] (throw (ex-info "Producer not trusted" {})))]
            (verifier/verify-report e instance (assoc report :status :fake-solver-success) p))]
    (println "LP-REPORT-VERIFIER" (pr-str r))
    (is (= :report-verified (:status r)))
    (is (= (set verifier/required-obligations) (set (keys (:verdicts r)))))
    (is (every? #(= #{} (:axioms %)) (vals (:verdicts r))))
    (is (string? (:audit/id r)))))

(deftest altered-reports-cannot-reuse-valid-proof-values
  (doseq [field [:achieved :bound :gap]]
    (let [r (verifier/verify-report @env instance (update report field inc) @proofs
                                    {:reductions 1000000})]
      (println "LP-REPORT-ALTERED" field (pr-str r))
      (is (= :rejected (:status r)))
      (is (= field (:failed-obligation r)))
      (is (= :kernel/type-mismatch
             (get-in r [:verdicts field :error/category]))))))

(deftest empty-missing-and-extra-evidence-never-reach-the-kernel
  (let [p @proofs]
    (doseq [bad (concat [{} (assoc p :extra (:gap p))]
                       (map #(dissoc p %) verifier/required-obligations))]
      (let [r (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Must reject shape first")))]
                (verifier/verify-report nil instance report bad))]
        (is (= :refused (:status r)))
        (is (= :lp-report/evidence-shape (:error/category r)))))))

(deftest resource-refusal-and-axiom-policy-cannot-be-reported-as-verified
  (let [e @env p @proofs]
    (doseq [response [{:status :rejected :error {:error/category :kernel/resource-limit}}
                     {:status :unexpected}]]
      (let [r (with-redefs [kernel/check (fn [& _] response)]
                (verifier/verify-report e instance report p))]
        (is (not= :report-verified (:status r)))
        (is (= :achieved (:failed-obligation r)))))
    (doseq [closure [nil #{'audit/untrusted-axiom}]]
      (let [r (with-redefs [kernel/axioms (fn [& _] closure)]
                (verifier/verify-report e instance report p))]
        (is (= :rejected (:status r)))
        (is (= :lp-report/axiom-policy
               (get-in r [:verdicts :achieved :error/category])))))))

(deftest malformed-data-and-huge-literals-are-refused-before-encoding
  (let [p @proofs]
    (doseq [[i r] [[(assoc instance :plan [1/2]) report]
                   [(assoc instance :matrix [[1] [0 1]]) report]
                   [instance (assoc report :achieved 18446744073709551617N)]
                   [instance (assoc report :gap 1.0)]
                   [instance (assoc report :direction :lower)]]]
      (let [result (verifier/verify-report nil i r p)]
        (is (= :refused (:status result)))
        (is (= :lp-report/input-shape (:error/category result)))))))
