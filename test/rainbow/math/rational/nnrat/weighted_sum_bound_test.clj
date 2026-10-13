(ns rainbow.math.rational.nnrat.weighted-sum-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.weighted-sum-bound :as bound]))
(deftest weighted-sum-bound-is-checked-and-axiom-free
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (bound/extend-environment (:environment cp))
        id (get (bound/theorem-ids env) 'nnrat/weighted-sum-at-most)
        d (environment/declaration env id)]
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
    (is (= #{} (kernel/axioms env id)))))
