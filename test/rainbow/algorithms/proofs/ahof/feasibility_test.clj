(ns rainbow.algorithms.proofs.ahof.feasibility-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.feasibility :as feasibility]
            [rainbow.algorithms.reference.feasibility :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          feasibility/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest feasibility-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (feasibility/definition-ids checked-environment)
        theorems (feasibility/theorem-ids checked-environment)]
    (is (= #{'feasibility/feasible?} (set (keys definitions))))
    (is (= #{'feasibility/feasible-cons
             'feasibility/all-satisfied-feasible
             'feasibility/one-violated-infeasible
             'feasibility/unconstrained-feasible}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-feasibility-and-csp-search
  (is (true? (executable/feasible? [true true])))
  (is (false? (executable/feasible? [true false true])))
  (is (true? (executable/feasible? [])))
  ;; Find x in 0..5 with x >= 2 and x <= 4: first feasible is 2.
  (is (= 2 (executable/solve (fn [x] [(>= x 2) (<= x 4)]) (range 6)))))
