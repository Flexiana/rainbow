(ns rainbow.or.lp-certificate-binary-tables-test
  "certify with {:table :binary}: instance data as balanced comparison trees, O(log n)
  steps per entry; the same verdicts as the default linear tables."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (-> (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz"))
             lp-on/extend-environment decide-order/extend-environment)))

(def ^:private c2
  {:sense :minimize
   :matrix [[1 1 1 0 0 0] [0 0 0 1 1 1] [-1 0 0 -1 0 0] [0 -1 0 0 -1 0] [0 0 -1 0 0 -1]]
   :capacities [18 8 -15 -2 -1] :margins [8 19 33 0 28 26]
   :plan [7 2 1 8 0 0] :prices [0 8 8 19 33]})

(deftest binary-tables-give-the-same-verdicts
  (doseq [proof [:composed :reflection]]
    (testing proof
      (let [linear (lp/certify @env c2 {:proof proof})
            binary (lp/certify @env c2 {:proof proof :table :binary})]
        (is (= :certified (:status linear) (:status binary)))
        (is (= 127 (:objective binary)))
        (is (every? empty? (map :axioms (vals (:declarations binary)))))
        (is (not= :certified (:status (lp/certify @env (assoc-in c2 [:prices 1] 9)
                                                  {:proof proof :table :binary :preflight? false}))))))))
