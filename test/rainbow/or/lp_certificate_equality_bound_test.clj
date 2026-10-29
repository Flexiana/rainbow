(ns rainbow.or.lp-certificate-equality-bound-test
  "Public-API regressions for the equality/integerization false-bound defect.
  These complement pure integerize tests with kernel-checked rejection and
  successful bounds in caller units, including negative free equality prices."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private base
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:status (:status checkpoint)})))
      (-> (:environment checkpoint) lp-on/extend-environment decide-order/extend-environment))))

(def ^:private invalid-certificate
  {:matrix [[1]] :capacities [1] :margins [1] :plan [1/2] :prices [2]
   :equalities [{:row [1] :value 1}] :equality-prices [-2]})

(defn- bound [instance]
  (lp/bound @base instance {:integerize? true :preflight? false}))

(deftest invalid-equality-certificate-is-rejected-through-the-public-api
  ;; Historically this returned an upper bound of 0, although the original
  ;; constraints admit x=1 with objective 1. The submitted x=1/2 is infeasible.
  (let [result (bound invalid-certificate)]
    (is (= :rejected (:status result)) (pr-str (dissoc result :data)))
    (is (some? (:kernel/category result))
        "The refusal must come from the kernel, not a preflight/setup refusal")
    (is (not= :kernel/resource-limit (:kernel/category result))
        "Exhausting resources is not verification of the invalid certificate")))

(defn- valid-result-checks [instance expected-bound expected-equality expected-price]
  (let [result (bound instance)
        verdicts (vals (:declarations result))]
    (is (= :bounded (:status result)) (pr-str (dissoc result :data)))
    (is (= 2 (:integer-scale result)))
    (is (= expected-bound (:bound result)) "Bound is in original caller units")
    (is (= 1 (:achieved result)))
    (is (= (- expected-bound 1) (:gap result)))
    (is (= :upper (:direction result)))
    (is (= instance (:instance result)))
    (is (= [expected-equality] (get-in result [:instance/checked :equalities])))
    (is (= [expected-price] (get-in result [:instance/checked :equality-prices])))
    (is (= 2 (count verdicts)) "Both submitted-plan and universal bound checks exist")
    (is (every? #(= :checked (:status %)) verdicts))
    (is (every? #(= #{} (:axioms %)) verdicts))))

(deftest valid-negative-free-price-and-fractional-equality-are-accepted
  (testing "equality is the only source of denominators; its negative price is valid"
    ;; x=1; dual 2 + (1/2)*(-2) = 1; bound 1*2 + (1/2)*(-2) = 1.
    (valid-result-checks
     {:matrix [[1]] :capacities [1] :margins [1] :plan [1] :prices [2]
      :equalities [{:row [1/2] :value 1/2}] :equality-prices [-2]}
     1 {:row [1] :value 2} -4)))

(deftest fractional-free-price-alone-triggers-scaling-and-retains-a-loose-bound
  (testing "a denominator occurring only in the free price still participates in D"
    ;; x=1; the feasible dual gives 3/2, a valid non-tight bound with gap 1/2.
    (valid-result-checks
     {:matrix [[1]] :capacities [1] :margins [1] :plan [1] :prices [1]
      :equalities [{:row [1] :value 1}] :equality-prices [1/2]}
     3/2 {:row [2] :value 4} 1)))
