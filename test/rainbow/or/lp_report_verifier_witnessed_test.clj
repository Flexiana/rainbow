(ns rainbow.or.lp-report-verifier-witnessed-test
  "Gate for the nine-obligation witnessed LP verification: the four report
  relations plus the five structural witnesses (primal/dual feasibility,
  primal/dual nonnegativity, universal reported bound), each replayed against a
  type reconstructed by the verifier -- never taken from the producer. Controls
  cover proof-reuse forgery across obligations, a below-optimal reported bound,
  altered report fields inside the bundle, wrong obligation counts, and a
  non-exact reported bound."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.lp-report-bridge :as report-producer]
            [rainbow.math.rational.signed.lp-witness-bridge :as witness-producer]
            [rainbow.or.lp-report-verifier :as verifier]))

(def ^:private instance
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [1 1]
   :plan [1/2 1/2] :prices [1 1]})
(def ^:private report {:achieved 1 :bound 2 :gap 1 :direction :upper})
(def ^:private reported-bound 2)

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint
                  "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (witness-producer/extend-environment (:environment r)))))

(defn- report-proofs [inst rep]
  (into {} (map (fn [[k spec]] [k (:value spec)]))
        (:specs (report-producer/report-specs inst rep))))
(defn- witness-proofs [inst bound]
  (into {} (map (fn [[k spec]] [k (:value spec)]))
        (witness-producer/witness-specs inst bound)))
(defn- all-proofs
  ([] (all-proofs instance report reported-bound))
  ([inst rep bound] (merge (report-proofs inst rep) (witness-proofs inst bound))))

(deftest nine-obligations-replay-verified-and-axiom-free
  (let [e @env
        p (all-proofs)
        ;; The producers are used only to MINT candidate proof values; the
        ;; verifier must not consult them for the expected types.
        r (with-redefs [report-producer/report-specs
                        (fn [& _] (throw (ex-info "report producer not trusted" {})))
                        witness-producer/witness-specs
                        (fn [& _] (throw (ex-info "witness producer not trusted" {})))]
            (verifier/verify-witnessed-report e instance report reported-bound p
                                              {:reductions 1000000}))]
    (println "LP-WITNESSED" (pr-str (dissoc r :verdicts)))
    (is (= :report-verified (:status r)))
    (is (= (set verifier/all-obligations) (set (keys (:verdicts r)))))
    (is (= 9 (count (:verdicts r))))
    (is (every? #(= #{} (:axioms %)) (vals (:verdicts r))))
    (is (= :maximization (:orientation r)))
    (is (= 2 (:reported-bound r)))
    (is (string? (:audit/id r)))))

(deftest a-proof-cannot-be-reused-for-a-different-obligation
  (let [e @env p (all-proofs)]
    (doseq [[wrong donor] [[:primal-feasibility :dual-feasibility]
                           [:universal-reported-bound :numeric-order]
                           [:dual-nonnegative :primal-feasibility]]]
      (let [bad (assoc p wrong (get p donor))
            r (verifier/verify-witnessed-report e instance report reported-bound bad
                                                {:reductions 1000000})]
        (println "LP-WITNESSED-REUSE" wrong (:status r) (:failed-obligation r))
        (is (= :rejected (:status r)) (pr-str [wrong r]))
        (is (= wrong (:failed-obligation r)))))))

(deftest reported-bound-below-the-attainable-optimum-is-rejected
  ;; Feasible candidate [1 1] attains objective 2, so a universal bound of 1 is
  ;; unsound: the reconstructed universal type at bound 1 cannot be satisfied.
  (let [e @env
        p (all-proofs instance report 1)
        r (verifier/verify-witnessed-report e instance report 1 p {:reductions 1000000})]
    (println "LP-WITNESSED-TOOLOW" (:status r) (:failed-obligation r))
    (is (= :rejected (:status r)))
    (is (= :universal-reported-bound (:failed-obligation r)))))

(deftest altered-report-fields-still-fail-inside-the-bundle
  (let [e @env]
    (doseq [field [:achieved :bound :gap]]
      (let [r (verifier/verify-witnessed-report
               e instance (update report field inc) reported-bound (all-proofs)
               {:reductions 1000000})]
        (is (= :rejected (:status r)))
        (is (= field (:failed-obligation r)))))))

(deftest wrong-obligation-count-is-refused-before-the-kernel
  (let [p (all-proofs)]
    (doseq [bad (concat [{} (assoc p :extra (:gap p))]
                        (map #(dissoc p %) verifier/all-obligations))]
      (let [r (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "shape first")))]
                (verifier/verify-witnessed-report nil instance report reported-bound bad))]
        (is (= :refused (:status r)))
        (is (= :lp-report/evidence-shape (:error/category r)))))))

(deftest non-exact-or-oversized-reported-bound-is-refused
  (let [p (all-proofs)]
    (doseq [bad [1.0 18446744073709551617N 10001 1/10001]]
      (let [r (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "shape first")))]
                (verifier/verify-witnessed-report nil instance report bad p))]
        (is (= :refused (:status r)) (pr-str bad))
        (is (= :lp-report/input-shape (:error/category r)))))))
