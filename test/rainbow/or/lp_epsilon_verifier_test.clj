(ns rainbow.or.lp-epsilon-verifier-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as f]
            [rainbow.math.rational.signed.lp-plan-report-bridge :as plan]
            [rainbow.math.rational.signed.lp-gap-quality-bridge :as producer]
            [rainbow.or.lp-certificate :as lp]
            [rainbow.or.lp-original-plan-verifier-test :as original-test]
            [rainbow.or.lp-original-plan-verifier :as verifier]))

(def ^:private env
  ;; Share the already-replayed immutable D63 base with the regression namespace
  ;; in the single modest-heap JVM; the old fixture is not mutated.
  (delay (producer/extend-environment @(var-get #'original-test/env))))
(def ^:private maximum {:matrix [[1]] :capacities [2] :margins [1] :prices [1] :plan [1]})
(def ^:private minimum {:matrix [[-1]] :capacities [-1] :margins [1] :prices [1] :plan [2] :sense :minimize})
(def ^:private report {:achieved 1 :bound 2 :gap 1 :direction :upper})
(def ^:private actual (#'lp/standard-form maximum))
(defn- values [specs] (into {} (map (fn [[k s]] [k (:value s)])) specs))
(defn- proofs [original a r epsilon] (values (producer/epsilon-specs original a r epsilon)))
(def ^:private evidence (delay (proofs maximum actual report 1)))
(defn- verify [original a r p epsilon]
  (verifier/verify @env original a r p {:claim :epsilon-plan :epsilon epsilon}))
(defn- show [label r]
  (println "LP-EPSILON-VERIFIER" label
           (pr-str (select-keys r [:status :claim :epsilon :failed-obligation :error/category :request/id :audit/id])))
  r)
(defn- accepted! [r epsilon]
  (is (= :original-plan-epsilon-verified (:status r)))
  (is (= :epsilon-plan (:claim r))) (is (= epsilon (:epsilon r)))
  (is (= verifier/epsilon-obligations (:required-obligations r)))
  (is (= 13 (count (:verdicts r))))
  (is (every? #(and (= :checked (:status %)) (= #{} (:axioms %))) (vals (:verdicts r))))
  (is (string? (:request/id r))) (is (string? (:audit/id r))))

(deftest independent-epsilon-replay-both-senses-and-boundary-fixtures
  (doseq [[label original r epsilon]
          [[:maximum maximum report 1]
           [:minimum minimum {:achieved 2 :bound 1 :gap 1 :direction :lower} 1]
           [:fractional (assoc maximum :plan [3/2]) {:achieved 3/2 :bound 2 :gap 1/2 :direction :upper} 1/2]
           [:equality {:matrix [] :capacities [] :margins [1 0] :plan [0 1] :prices []
                       :equalities [{:row [1 1] :value 1}] :equality-prices [1]}
            {:achieved 0 :bound 1 :gap 1 :direction :upper} 1]
           [:zero (assoc maximum :plan [2]) {:achieved 2 :bound 2 :gap 0 :direction :upper} 0]
           [:empty {:matrix [] :capacities [] :margins [] :plan [] :prices []}
            {:achieved 0 :bound 0 :gap 0 :direction :upper} 0]]]
    (let [a (#'lp/standard-form original) p (proofs original a r epsilon) e @env
          result (with-redefs [producer/epsilon-specs (fn [& _] (throw (AssertionError. "Producer called")))
                              plan/plan-report-specs (fn [& _] (throw (AssertionError. "Producer called")))]
                   (verifier/verify e original a r p {:claim :epsilon-plan :epsilon epsilon}))]
      (accepted! (show label result) epsilon))))

(deftest same-cardinality-does-not-make-claims-interchangeable
  (let [p @evidence exact (values (plan/optimality-specs maximum actual report))]
    (is (= 13 (count p) (count exact)))
    (doseq [[proofs options] [[p {:claim :optimal-plan}]
                              [exact {:claim :epsilon-plan :epsilon 1}]
                              [p {}]]]
      (let [r (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Coverage first")))]
                (verifier/verify nil maximum actual report proofs options))]
        (is (= :refused (:status r)))
        (is (= :lp-original-plan/evidence-shape (:error/category r)))))))

(deftest epsilon-is-bound-into-request-target-and-audit-identities
  (let [p1 @evidence p2 (proofs maximum actual report 2)
        r1 (show :epsilon-one (verify maximum actual report p1 1))
        r2 (show :epsilon-two (verify maximum actual report p2 2))
        repeat-r1 (verify maximum actual report p1 1)]
    (accepted! r1 1) (accepted! r2 2)
    (is (= r1 repeat-r1))
    (is (not= (:request/id r1) (:request/id r2)))
    (is (not= (:audit/id r1) (:audit/id r2)))
    (doseq [key [:gap-within-budget :epsilon-optimal]]
      (is (not= (get-in r1 [:verdicts key :type/id]) (get-in r2 [:verdicts key :type/id]))))
    (doseq [requested [0 2]]
      (let [r (show [:stale-epsilon requested] (verify maximum actual report p1 requested))]
        (is (= :rejected (:status r))) (is (= :gap-within-budget (:failed-obligation r)))
        (is (= :kernel/type-mismatch (get-in r [:verdicts :gap-within-budget :error/category])))))))

(deftest every-epsilon-obligation-must-be-present-and-checked
  (let [p @evidence e @env]
    (doseq [k verifier/epsilon-obligations]
      (let [missing (with-redefs [kernel/check (fn [& _] (throw (AssertionError. "Coverage first")))]
                      (verifier/verify nil maximum actual report (dissoc p k) {:claim :epsilon-plan :epsilon 1}))
            corrupt (show [:corrupt k]
                          (verifier/verify e maximum actual report (assoc p k (f/const* 'proposition/trivial []))
                                           {:claim :epsilon-plan :epsilon 1}))]
        (is (= :lp-original-plan/evidence-shape (:error/category missing)))
        (is (= :rejected (:status corrupt))) (is (= k (:failed-obligation corrupt)))
        (is (= :kernel/type-mismatch (get-in corrupt [:verdicts k :error/category])))))))

(deftest invalid-epsilon-and-inapplicable-epsilon-refused-before-encoding
  (let [p @evidence]
    (doseq [options (concat [{:claim :epsilon-plan} {:claim :optimal-plan :epsilon 0}
                            {:epsilon 0} {:claim :feasible-report :epsilon nil}]
                           (map #(hash-map :claim :epsilon-plan :epsilon %)
                                [nil -1 0.5 ##NaN 1/10001 18446744073709551616N]))]
      (let [r (with-redefs-fn {#'lp/signed-literal (fn [& _] (throw (AssertionError. "Encoder reached")))
                              #'kernel/check (fn [& _] (throw (AssertionError. "Kernel reached")))}
                #(verifier/verify nil maximum actual report p options))]
        (is (= :refused (:status r))) (is (= :lp-original-plan/options (:error/category r)))))))

(deftest true-quality-inequality-does-not-override-infeasibility
  (let [original (assoc maximum :plan [-1]) a (#'lp/standard-form original)
        r {:achieved -1 :bound 2 :gap 3 :direction :upper}
        result (show :infeasible (verify original a r (proofs original a r 3) 3))]
    (is (= :rejected (:status result))) (is (= :submitted-plan-feasible (:failed-obligation result))))
  (let [p (proofs maximum actual report 0) r (show :false-budget (verify maximum actual report p 0))]
    (is (= :rejected (:status r))) (is (= :gap-within-budget (:failed-obligation r)))))

(deftest late-resource-failure-never-upgrades-a-partial-certificate
  ;; Policy fault injection, not a mathematical rejection or a resource benchmark.
  (let [p @evidence e @env real-check kernel/check calls (atom 0)
        r (with-redefs [kernel/check (fn [& args]
                                      (if (= 13 (swap! calls inc))
                                        {:status :rejected :error {:error/category :kernel/resource-limit}}
                                        (apply real-check args)))]
            (verifier/verify e maximum actual report p {:claim :epsilon-plan :epsilon 1}))]
    (is (= 13 @calls)) (is (= :refused (:status r)))
    (is (= :epsilon-optimal (:failed-obligation r)))
    (is (= :kernel/resource-limit (get-in r [:verdicts :epsilon-optimal :error/category])))))

(deftest legacy-exact-optimality-identity-is-unchanged
  (let [original (assoc maximum :plan [2]) a (#'lp/standard-form original)
        r {:achieved 2 :bound 2 :gap 0 :direction :upper}
        p (values (plan/optimality-specs original a r))
        result (verifier/verify @env original a r p {:claim :optimal-plan})
        basic (verifier/verify @env original a r (select-keys p verifier/report-obligations))]
    (is (= :original-plan-optimal (:status result)))
    ;; Pinned successful d393c80 maximum fixture before the epsilon API existed. The audit
    ;; ids changed once, deliberately, on 2026-10-16 when certificates began writing their
    ;; numbers as kernel literals (approved by Jiri); before: 32a3a843... and 82b68f82....
    (is (= "sha256:b3889ba4710cb81661528337fa11acd9754bf6d3fdfd7eaeffa0905382c66d35" (:request/id result)))
    (is (= "sha256:fed9d0e9a101c375a1bb13f5d30af24124c5bf6b6187b9a856ad02b4403af7e0" (:audit/id result)))
    (is (not (contains? result :epsilon)))
    (is (= :original-plan-report-verified (:status basic)))
    (is (= (:request/id result) (:request/id basic)))
    (is (= "sha256:6d66b4994d20c2dc57068990ab0b63bf0a4316db830cccd4e64e6a763c582df8" (:audit/id basic)))))
