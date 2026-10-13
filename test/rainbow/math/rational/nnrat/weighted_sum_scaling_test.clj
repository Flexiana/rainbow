(ns rainbow.math.rational.nnrat.weighted-sum-scaling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.weighted-sum-scaling :as scaling]))
(deftest weighted-sum-scaling-is-checked-and-axiom-free
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (scaling/extend-environment (:environment cp))
        id (get (scaling/theorem-ids env) 'nnrat/weighted-sum-scaling)
        d (environment/declaration env id)]
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
    (is (= #{} (kernel/axioms env id)))))
