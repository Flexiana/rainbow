(ns rainbow.math.rational.nnrat.weighted-term-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.weighted-term-bound :as bound]))
(deftest weighted-term-bound-is-checked-and-axiom-free
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (bound/extend-environment (:environment cp))
        id (get (bound/theorem-ids env) 'nnrat/weighted-term-at-most)
        d (environment/declaration env id)]
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{}))))
    (is (= #{} (kernel/axioms env id)))))
