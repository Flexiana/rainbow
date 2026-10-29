(ns rainbow.or.lp-certificate-reflection-mode-test
  "certify with {:proof :reflection}: the same claims, proved by one application of
  lp/certificate-check-sound instead of one proof per row and column."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.lp-duality-on :as lp-on]
            [rainbow.or.lp-certificate :as lp]))

(def ^:private env
  (delay (-> (:environment (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz"))
             lp-on/extend-environment decide-order/extend-environment)))

;; RH2EDIN Reto 2, trailer allocation (c2): minimum cost 127
(def ^:private c2
  {:sense :minimize
   :matrix [[1 1 1 0 0 0] [0 0 0 1 1 1] [-1 0 0 -1 0 0] [0 -1 0 0 -1 0] [0 0 -1 0 0 -1]]
   :capacities [18 8 -15 -2 -1] :margins [8 19 33 0 28 26]
   :plan [7 2 1 8 0 0] :prices [0 8 8 19 33]})

(defn- nodes [t] (count (filter #(and (vector? %) (keyword? (first %))) (tree-seq vector? seq t))))
(defn- declaration [result alias]
  (environment/declaration (:environment result) (get-in result [:declarations alias :id])))

(deftest reflection-proves-the-same-claims
  (let [composed (lp/certify @env c2)
        reflected (lp/certify @env c2 {:proof :reflection})]
    (is (= :certified (:status composed)))
    (is (= :certified (:status reflected)))
    (is (= 127 (:objective composed) (:objective reflected)))
    (is (= :reflection (:proof reflected)))
    (is (= :composed (:proof composed)))
    (is (some #{'rainbow.math.rational.signed.lp-certificate-reflect} (:bundle/modules reflected)))
    (doseq [alias ['optimization/lp-instance-optimal 'optimization/lp-instance-optimal-value]]
      (testing alias
        (is (= (:rainbow/type (declaration composed alias)) (:rainbow/type (declaration reflected alias))))
        (is (= #{} (get-in reflected [:declarations alias :axioms])))))
    (let [composed-nodes (nodes (:rainbow/value (declaration composed 'optimization/lp-instance-optimal)))
          reflected-nodes (nodes (:rainbow/value (declaration reflected 'optimization/lp-instance-optimal)))]
      (is (< (* 10 reflected-nodes) composed-nodes) [reflected-nodes composed-nodes]))))

(deftest reflection-rejects-a-changed-price
  (let [r (lp/certify @env (assoc-in c2 [:prices 1] 9) {:proof :reflection :preflight? false})]
    (is (not= :certified (:status r)))))
