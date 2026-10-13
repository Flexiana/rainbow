(ns rainbow.math.finite.async-value-iteration-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.async-value-iteration :as ahof-d23]
            [rainbow.math.finite.async-value-iteration :as iteration]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d22-value-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D22 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d23/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest finite-async-value-iteration-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'value/nnrat-async-update
             'value/nnrat-async-iterate}
           (set (keys definitions))))
    (is (= #{'value/nnrat-async-update-selected
             'value/nnrat-async-update-preserved
             'value/nnrat-async-iterate-zero
             'value/nnrat-async-iterate-successor
             'value/nnrat-async-update-selected-dominates
             'value/nnrat-async-state-schedule-transfer}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d23-package-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        definitions (ahof-d23/definition-ids checked-environment)
        theorems (ahof-d23/theorem-ids checked-environment)]
    (is (= #{'ahof-d23/schedule
             'ahof-d23/async-sequence
             'ahof-d23/one-step-async
             'ahof-d23/two-step-async}
           (set (keys definitions))))
    (is (= #{'ahof-d23/schedule-selects-zero
             'ahof-d23/schedule-skips-one
             'ahof-d23/selected-update
             'ahof-d23/preserved-update
             'ahof-d23/async-recurrence
             'ahof-d23/greedy-actions
             'ahof-d23/two-step-async-values
             'ahof-d23/async-value-iteration}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))
