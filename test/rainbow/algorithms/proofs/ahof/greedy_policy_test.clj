(ns rainbow.algorithms.proofs.ahof.greedy-policy-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.greedy-policy :as greedy]
            [rainbow.algorithms.reference.greedy-policy :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          greedy/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest greedy-policy-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (greedy/definition-ids checked-environment)
        theorems (greedy/theorem-ids checked-environment)]
    (is (= #{'greedy/action 'greedy/value} (set (keys definitions))))
    (is (= #{'greedy/action-example 'greedy/value-example
             'greedy/dominates-action-zero 'greedy/dominates-action-two}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-greedy-policy-selects-best
  (is (= 1 (executable/greedy-action [5 7 4])))
  (is (= 7 (executable/greedy-value [5 7 4])))
  (is (= 0 (executable/greedy-action [9 2 3])))
  (is (= 9 (executable/greedy-value [9 2 3]))))
