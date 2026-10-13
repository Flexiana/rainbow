(ns rainbow.math.finite.markov-mixture-statement-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-mixture-statement :as statement]))

(deftest mixture-target-is-well-formed-and-unproved
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (statement/extend-environment (:environment cp))
        id (get (statement/definition-ids env) 'markov/nnrat-finite-mixture-bound)
        d (environment/declaration env id)]
    (is (= :definition (:rainbow/kind d)))
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
    (is (= #{} (kernel/axioms env id)))
    (is (empty? (statement/theorem-ids env)))))
