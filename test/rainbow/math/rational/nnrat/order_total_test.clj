(ns rainbow.math.rational.nnrat.order-total-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.rational.nnrat.order-total :as total]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (total/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest nnrat-order-is-total
  (testing "prerequisite for the recursive-reduction sub-brick: the nnrat
            order is total -- for all a b, a <= b OR b <= a. Case-split on
            the boolean decision (Bool.rec), true -> a<=b, false -> b<=a
            (decide-at-most-false-reverse). Kernel-checked, axiom-free"
    (let [env @checked-environment
          ids (merge (total/definition-ids env) (total/theorem-ids env))]
      (is (= #{'nnrat/at-most-total}
             (set (keys ids))))
      (doseq [[name id] ids]
        (is (some? id) (str name))
        (is (checked? env id) (str name))
        (is (= #{} (kernel/axioms env id)) (str name))))))
