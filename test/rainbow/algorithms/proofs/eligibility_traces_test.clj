(ns rainbow.algorithms.proofs.eligibility-traces-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.eligibility-traces :as ahof-d63]
            [rainbow.algorithms.proofs.eligibility-traces :as iteration]
            [rainbow.algorithms.reference.eligibility-traces :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint "artifacts/ahof/d62-sarsa/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D62 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d63/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest eligibility-traces-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'learning/eligibility-trace-update 'learning/trace-weighted-update}
           (set (keys definitions))))
    (is (= #{'learning/eligibility-trace-update-unfold
             'learning/trace-weighted-update-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d63-eligibility-traces-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d63/theorem-ids checked-environment)]
    (is (= #{'ahof-d63/trace-is-three-halves
             'ahof-d63/value-is-one-half
             'ahof-d63/eligibility-traces}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-eligibility-traces-decay-and-weight-the-update
  ;; Decay 1/2, trace 1: the visited state's trace becomes (1/2)*1 + 1 = 3/2.
  ;; Rate 1/2, TD error 1, value 0: the trace-weighted update raises the value by
  ;; (1/2)*1 = 1/2.
  (is (= 3/2 (executable/trace-update 1/2 1)))
  (is (= 1/2 (executable/trace-weighted-update 1/2 1 1 0)))
  ;; A larger trace assigns more credit.
  (is (= 1 (executable/trace-weighted-update 1/2 2 1 0))))
