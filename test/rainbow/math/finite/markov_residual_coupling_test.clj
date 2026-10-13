(ns rainbow.math.finite.markov-residual-coupling-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-residual-coupling :as target]))
(def checked-environment
  (delay
    (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status cp))
        (throw (ex-info "D63 replay failed" {:status (:status cp)})))
      (target/extend-environment (:environment cp)))))
(deftest residual-balance-and-product-marginals-are-checked
  (let [env @checked-environment
        ids (merge (target/definition-ids env) (target/theorem-ids env))]
    (is (= 6 (count ids)))
    (doseq [[name id] ids]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))
