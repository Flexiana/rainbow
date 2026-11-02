(ns rainbow.or.lp-min-long-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]))

(defn nnrat [n] [:app [:const 'nnrat/make []] [:nat n] [:nat 0]])

(deftest minimum-long-coefficient-encodes-its-exact-magnitude
  (is (= [:app [:const 'signed/make []] (nnrat 0) (nnrat 9223372036854775808N)]
         (#'lp/signed-literal Long/MIN_VALUE))))

(deftest ordinary-coefficients-retain-their-encoding
  (is (= [:app [:const 'signed/make []] (nnrat 7) (nnrat 0)]
         (#'lp/signed-literal 7)))
  (is (= [:app [:const 'signed/make []] (nnrat 0) (nnrat 7)]
         (#'lp/signed-literal -7))))

;; B-20261102-1: the 1.5.2 fix above reached the literal encoder only. The cost estimate certify runs
;; first (preflight, on by default), the minimize and equality rewrites and the reported objective
;; negated and multiplied Longs with overflow-checked arithmetic, so these valid, optimal certificates
;; threw `ArithmeticException: long overflow` out of certify and bound.

(def ^:private two-63 9223372036854775808N)

(def ^:private overflowing
  {"a -2^63 margin" {:matrix [[1]] :capacities [1] :margins [Long/MIN_VALUE] :plan [0] :prices [0]}
   ;; minimize -2^63 x, x <= 1: x = 1, the price 2^63 proves no plan costs less
   "a -2^63 cost when minimizing" {:matrix [[1]] :capacities [1] :margins [Long/MIN_VALUE] :sense :minimize
                                    :plan [1] :prices [two-63]}
   ;; maximize x, x <= 2^63, -x = -2^63
   "a -2^63 equality value" {:matrix [[1]] :capacities [two-63] :margins [1] :plan [two-63] :prices [1]
                             :equalities [{:row [-1] :value Long/MIN_VALUE}] :equality-prices [0]}
   ;; maximize 2^32 x, x <= 2^64: the objective 2^96 is past a Long
   "an objective past 2^63" {:matrix [[1]] :capacities [18446744073709551616N] :margins [4294967296]
                             :plan [18446744073709551616N] :prices [4294967296]}})

(deftest preflight-estimates-instances-beyond-a-long
  (doseq [[label instance] overflowing]
    (testing label
      (is (#{:fits :marginal :over-budget} (:verdict (lp/preflight instance)))))))

(def ^:private env
  (delay (-> (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz"))
             lp-on/extend-environment decide-order/extend-environment)))

(defn- alias-for [label suffix] (symbol "optimization" (str "min-long-" (Math/abs (long (hash label))) suffix)))

(deftest certify-answers-instead-of-throwing-beyond-a-long
  (doseq [[label instance] overflowing]
    (testing label
      ;; with the estimate on, a refusal is an answer; an exception is not
      (is (#{:certified :rejected} (:status (lp/certify @env instance {:alias (alias-for label "-p")}))))
      (let [r (lp/certify @env instance {:alias (alias-for label "") :preflight? false})]
        (is (= :certified (:status r)) (pr-str (dissoc r :environment)))))))

(deftest certified-numbers-are-exact-beyond-a-long
  (let [r (lp/certify @env (overflowing "an objective past 2^63") {:alias 'optimization/min-long-objective :preflight? false})]
    (is (= :certified (:status r)))
    (is (= 79228162514264337593543950336N (:objective r)))))
