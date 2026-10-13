(ns rainbow.math.finite.markov-coupling-coefficient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.markov-coupling-coefficient :as target]))
(def checked-environment (delay
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
    (when-not (= :replayed (:status cp)) (throw (ex-info "D63 replay failed" {})))
    (target/extend-environment (:environment cp)))))
(deftest coupling-cost-and-positive-contraction-are-kernel-checked
  (let [env @checked-environment]
    (doseq [[name id] (target/theorem-ids env)]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))
