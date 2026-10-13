(ns rainbow.algorithms.proofs.ahof.fuzzing-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.fuzzing :as fuzzing]
            [rainbow.algorithms.reference.fuzzing :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          fuzzing/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest fuzzing-flip-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (fuzzing/definition-ids checked-environment)
        theorems (fuzzing/theorem-ids checked-environment)]
    (is (= #{'fuzzing/flip} (set (keys definitions))))
    (is (= #{'fuzzing/flip-true 'fuzzing/flip-false
             'fuzzing/flip-involution-true 'fuzzing/flip-involution-false}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-fuzzing-finds-violations
  (is (false? (executable/flip true)))
  (is (true? (executable/flip false)))
  (is (= [true false false] (executable/mutate [false false false] 0)))
  ;; Spec: "not all bits set". Fuzzing [true true false] flips bit 2 -> all true,
  ;; violating the spec.
  (let [spec? (fn [bits] (not (every? true? bits)))
        violation (executable/fuzz spec? [true true false])]
    (is (= [true true true] violation))))
