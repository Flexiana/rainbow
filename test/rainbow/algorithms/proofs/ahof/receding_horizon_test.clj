(ns rainbow.algorithms.proofs.ahof.receding-horizon-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.receding-horizon :as mpc]
            [rainbow.algorithms.reference.receding-horizon :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          mpc/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest receding-horizon-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (mpc/definition-ids checked-environment)
        theorems (mpc/theorem-ids checked-environment)]
    (is (= #{'mpc/first-action} (set (keys definitions))))
    (is (= #{'mpc/first-action-cons
             'mpc/first-action-example
             'mpc/first-action-empty}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-receding-horizon-applies-first-actions
  (is (= 5 (executable/first-action 0 [5 2 8])))
  (is (= 0 (executable/first-action 0 [])))
  ;; A greedy 1-step plan toward target 3 from state 0: each step moves +1, so
  ;; the applied actions drive the state to the target and then hold.
  (let [plan-fn (fn [s] (if (< s 3) [1 1] [0]))
        dynamics (fn [s a] (+ s a))
        actions (executable/control plan-fn dynamics 0 0 5)]
    (is (= [1 1 1 0 0] actions))))
