(ns rainbow.math.finite.value-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.value-iteration :as ahof-d22]
            [rainbow.math.finite.value-iteration :as iteration]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d21-policy-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D21 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d22/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-value-iteration-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'bellman/nnrat-action-backup
             'value/nnrat-greedy-action
             'value/nnrat-optimality-step
             'value/nnrat-iterate}
           (set (keys definitions))))
    (is (= #{'bellman/nnrat-action-backup-unfold
             'value/nnrat-greedy-action-is-admissible
             'value/nnrat-optimality-step-dominates
             'value/nnrat-optimality-step-unfold
             'value/nnrat-iterate-zero
             'value/nnrat-iterate-successor
             'value/nnrat-optimality-state-transfer}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d22-package-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (ahof-d22/definition-ids checked-environment)
        theorems (ahof-d22/theorem-ids checked-environment)]
    (is (= 11 (count definitions)))
    (is (= #{'ahof-d22/fallback-action-admissible
             'ahof-d22/action-backup-correspondence
             'ahof-d22/normalized-transition-rows
             'ahof-d22/finite-horizon-recurrence
             'ahof-d22/greedy-actions
             'ahof-d22/two-step-value
             'ahof-d22/value-iteration}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
