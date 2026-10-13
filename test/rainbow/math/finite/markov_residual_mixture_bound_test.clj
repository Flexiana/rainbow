(ns rainbow.math.finite.markov-residual-mixture-bound-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-residual-mixture-bound :as target]))

(deftest residual-mixture-bound-is-checked-and-axiom-free
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (target/extend-environment (:environment cp))
        id (get (target/theorem-ids env) 'markov/nnrat-finite-residual-mixture-bound)
        d (environment/declaration env id)]
    (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
    (is (= #{} (kernel/axioms env id)))))
