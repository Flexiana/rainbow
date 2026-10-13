(ns rainbow.math.rational.nnrat.map-sum-on-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.fixtures.nnrat-map-sum-on-independent :as independent]
            [rainbow.math.rational.nnrat.map-sum-on :as target]))
(deftest support-restricted-monotonicity-is-kernel-checked
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        _ (is (= :replayed (:status cp)))
        env (target/extend-environment (:environment cp))]
    (doseq [[name id] (target/theorem-ids env)]
      (let [d (environment/declaration env id)]
        (is (some? id) (str name))
        (is (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d) #{'u}))))
        (is (= #{} (kernel/axioms env id)))))))

(deftest duplicate-construction-is-not-a-stronger-statement
  (let [cp (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")
        env (target/extend-environment (:environment cp))
        original independent/map-sum-monotone-on-spec
        type-result (elaborate/core-expression env (:type original))
        proof-result (elaborate/core-expression env (:value original))
        id (environment/resolve-id env 'nnrat/map-sum-monotone-on)
        canonical (environment/declaration env id)]
    (is (= :elaborated (:status type-result)))
    (is (= :elaborated (:status proof-result)))
    (is (= (:term type-result) (:rainbow/type canonical)))
    (is (= :checked (:status (kernel/check env (:term proof-result) (:rainbow/type canonical) #{'u}))))
    (is (= (metric/theorem-ids env) (metric/theorem-ids (target/extend-environment env))))))
