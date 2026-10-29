(ns rainbow.or.lp-minimization-verifier-test
  "Gate for independent minimization lower-bound verification: verify-minimization-lower-bound
  reconstructs the universal original-cost target itself and replays the bridge's proof.
  Controls: a below-true-minimum (too-high) lower bound is rejected, a maximization instance
  is refused, and a non-exact lower bound is refused before the kernel."
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.signed.lp-minimization-bridge :as bridge]
            [rainbow.or.lp-report-verifier :as verifier]))

(def ^:private one-col
  {:matrix [[1]] :capacities [1] :margins [-1] :plan [1/2] :prices [1] :sense :minimize})
(def ^:private mixed
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [2 -1]
   :plan [0 1/2] :prices [0 1] :sense :minimize})

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (bridge/extend-environment (:environment r)))))

(defn- lower-bound-proof [instance lower]
  (:value (:universal-original-lower-bound (bridge/minimization-specs instance lower))))

(deftest sound-lower-bound-is-independently-verified
  (let [e @env]
    (doseq [instance [one-col mixed]]
      (let [proof (lower-bound-proof instance -1)
            r (with-redefs [bridge/minimization-specs
                            (fn [& _] (throw (ex-info "producer not trusted" {})))]
                (verifier/verify-minimization-lower-bound e instance -1 proof {:reductions 1000000}))]
        (println "LP-MIN-VERIFY" (:margins instance) (pr-str (dissoc r :verdict)))
        (is (= :minimization-bound-verified (:status r)) (pr-str r))
        (is (= :minimization (:orientation r)))
        (is (= -1 (:lower r)))
        (is (= #{} (get-in r [:verdict :axioms])))
        (is (string? (:audit/id r)))))))

(deftest too-high-lower-bound-is-rejected
  ;; Feasible candidate [0 1] has original cost -1, so a universal lower bound of 0 is false.
  (let [e @env
        proof (lower-bound-proof mixed 0)
        r (verifier/verify-minimization-lower-bound e mixed 0 proof {:reductions 1000000})]
    (println "LP-MIN-TOOHIGH" (pr-str (dissoc r :verdict)))
    (is (= :rejected (:status r)))
    (is (= :kernel/type-mismatch (:error/category r)))))

(deftest maximization-instance-is-refused
  (let [e @env
        proof (lower-bound-proof mixed -1)
        r (verifier/verify-minimization-lower-bound e (assoc mixed :sense :maximize) -1 proof)]
    (is (= :refused (:status r)))
    (is (= :lp-minimization/wrong-sense (:error/category r)))))

(deftest non-exact-lower-bound-is-refused-before-the-kernel
  (let [proof (lower-bound-proof mixed -1)]
    (doseq [bad [1.0 18446744073709551617N 10001]]
      (let [r (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "shape first")))]
                (verifier/verify-minimization-lower-bound nil mixed bad proof))]
        (is (= :refused (:status r)) (pr-str bad))
        (is (= :lp-report/input-shape (:error/category r)))))))
