(ns rainbow.algorithms.proofs.ahof.penalty-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.penalty :as penalty]
            [rainbow.algorithms.reference.penalty :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          penalty/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest penalty-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (penalty/definition-ids checked-environment)
        theorems (penalty/theorem-ids checked-environment)]
    (is (= #{'penalty/penalized} (set (keys definitions))))
    (is (= #{'penalty/penalized-example 'penalty/feasible-equals-objective}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-penalty-method
  (is (= 5 (executable/penalized 2 3 1)))
  (is (= 2 (executable/penalized 2 3 0)))
  ;; increasing mu penalizes an infeasible point more and more
  (is (= [3 5 12] (executable/penalty-path 2 1 [1 3 10]))))
