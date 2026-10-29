(ns rainbow.math.rational.signed.lp-witness-bridge-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.math.rational.signed.lp-witness-bridge :as witness]))

(def ^:private env
  (delay (let [r (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status r)) (throw (ex-info "Checkpoint failed" {})))
           (witness/extend-environment (:environment r)))))
(def ^:private instance
  {:matrix [[1 0] [0 1]] :capacities [1 1] :margins [1 1]
   :plan [1/2 1/2] :prices [1 1]})
(defn- core! [expression]
  (let [r (elaborate/core-expression @env expression)]
    (when-not (= :elaborated (:status r))
      (throw (ex-info "Witness did not elaborate" {:result r})))
    (:term r)))
(defn- check [label spec]
  (let [v (core! (:value spec)) t (core! (:type spec))
        r (binding [kernel/*reduction-budget* 1000000] (kernel/check @env v t #{}))
        closures (when (= :checked (:status r))
                   (map #(kernel/axioms @env %) (into (term/constants v) (term/constants t))))
        result {:status (:status r) :category (get-in r [:error :error/category])
                :axioms (when (and (= :checked (:status r)) (every? set? closures))
                          (into #{} cat closures))}]
    (println "LP-WITNESS" label (pr-str result))
    result))
(defn- checked! [label spec]
  (let [r (check label spec)]
    (is (= :checked (:status r)) (pr-str r))
    (is (= #{} (:axioms r)))))
(defn- rejected! [label spec]
  (let [r (check label spec)]
    (is (= :rejected (:status r)) (pr-str r))
    (is (= :kernel/type-mismatch (:category r)) (pr-str r))))

(deftest original-witnesses-and-universal-reported-bound
  (doseq [[label spec] (witness/witness-specs instance 2)]
    (checked! label spec)))

(deftest minimization-witnesses-and-negated-universal-endpoint
  (let [i {:matrix [[1]] :capacities [1] :margins [-1]
           :plan [1/2] :prices [1] :sense :minimize}]
    (doseq [[label spec] (witness/witness-specs i -1)]
      (checked! [:minimize label] spec))))

(deftest infeasible-plan-does-not-destroy-a-valid-dual-bound
  (let [specs (witness/witness-specs (assoc instance :plan [2 1/2]) 2)]
    (rejected! :false-primal (:primal-feasibility specs))
    (checked! :universal-independent-of-submitted-plan (:universal-reported-bound specs))))

(deftest false-dual-and-too-low-reported-endpoint-are-rejected
  (let [specs (witness/witness-specs (assoc instance :prices [0 1]) 1)]
    (rejected! :false-dual (:dual-feasibility specs))
    (rejected! :false-dual-universal (:universal-reported-bound specs)))
  ;; Submitted objective is 1, so an actual-plan comparison alone permits 1.
  ;; But feasible candidate [1 1] attains 2: the universal bound cannot be 1.
  (rejected! :too-low-universal
             (:universal-reported-bound (witness/witness-specs instance 1))))

(deftest negative-primal-and-dual-components-cannot-supply-nonnegativity
  (rejected! :negative-plan
             (:primal-nonnegative (witness/witness-specs (assoc instance :plan [-1/2 1/2]) 2)))
  (rejected! :negative-price
             (:dual-nonnegative (witness/witness-specs (assoc instance :prices [-1 1]) 0))))
