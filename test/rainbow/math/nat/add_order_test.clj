(ns rainbow.math.nat.add-order-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.nat.add-order :as nao]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (nao/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest nat-additive-monotonicity-is-axiom-free
  (let [env @checked-environment
        theorems (nao/theorem-ids env)]
    (is (= #{'nat/le-add-right 'nat/le-add-self} (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))
