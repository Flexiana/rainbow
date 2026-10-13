(ns rainbow.math.linear.vector.equivalence-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.linear.vector.equivalence :as veq]))

(def checked-environment
  (delay
    (let [checkpoint (checkpoint/load-checkpoint
                      "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (veq/extend-environment (:environment checkpoint)))))

(defn- checked? [env id]
  (let [d (environment/declaration env id)]
    (= :checked (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                       (set (:rainbow/universes d)))))))

(deftest vector-equivalence-is-native-axiom-free
  (let [env @checked-environment
        definitions (veq/definition-ids env)
        theorems (veq/theorem-ids env)]
    (is (= #{'vector/equivalent} (set (keys definitions))))
    (is (= #{'vector/nil-equivalent 'vector/reflexive-example
             'vector/subtract-equivalent-example
             'vector/nil-cons-not-equivalent 'vector/cons-nil-not-equivalent}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms env id)) (str name))
      (is (checked? env id) (str name)))))
