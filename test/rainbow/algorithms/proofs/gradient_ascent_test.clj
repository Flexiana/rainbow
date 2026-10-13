(ns rainbow.algorithms.proofs.gradient-ascent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gradient-ascent :as ahof-d49]
            [rainbow.algorithms.proofs.gradient-ascent :as iteration]
            [rainbow.algorithms.reference.gradient-ascent :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d23-async-value-iteration/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D23 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d49/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest gradient-ascent-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/nnrat-ascent-step
             'optimization/nnrat-ascent-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/nnrat-ascent-step-unfold
             'optimization/nnrat-ascent-iterate-zero
             'optimization/nnrat-ascent-iterate-successor
             'optimization/nnrat-ascent-step-transfer}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d49-trajectory-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d49/theorem-ids checked-environment)]
    (is (= #{'ahof-d49/gradient-ascent-recurrence
             'ahof-d49/worked-trajectory
             'ahof-d49/gradient-ascent}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-reference-matches-the-worked-rational-trajectory
  ;; Constant unit gradient, rate 1/2, from the origin: exactly n/2 after n steps.
  (is (= [0 1/2 1 3/2 2]
         (executable/trajectory (constantly 1) 1/2 0 4)))
  ;; A pluggable nonconstant gradient still steps exactly.
  (is (= 3/4 (executable/ascent-iterate (fn [x] (- 1 x)) 1/2 1 1/2))))
