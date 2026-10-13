(ns rainbow.algorithms.proofs.gradient-descent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.gradient-descent :as ahof-o17]
            [rainbow.algorithms.proofs.gradient-descent :as iteration]
            [rainbow.algorithms.reference.gradient-descent :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d19-value-of-information/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D19 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o17/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest signed-gradient-descent-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/signed-descent-step
             'optimization/signed-descent-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/signed-descent-step-unfold
             'optimization/signed-descent-iterate-zero
             'optimization/signed-descent-iterate-successor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o17-descent-reaches-negative-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o17/theorem-ids checked-environment)]
    (is (= #{'ahof-o17/trajectory-values
             'ahof-o17/descent-recurrence
             'ahof-o17/gradient-descent}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-descent-reaches-negative-values-exactly
  ;; Constant unit gradient, rate 1/2, from 1: exactly 1 - n/2, going negative.
  (is (= [1 1/2 0 -1/2 -1]
         (executable/trajectory 1/2 (constantly 1) 1 4)))
  ;; A nonconstant gradient still steps exactly.
  (is (= 3/4 (executable/descent-iterate 1/2 (fn [x] (/ 1 2)) 1 1))))
