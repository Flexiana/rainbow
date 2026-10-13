(ns rainbow.math.temporal-difference-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.q-learning :as ahof-d61]
            [rainbow.math.temporal-difference :as iteration]
            [rainbow.algorithms.reference.q-learning :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o17-gradient-descent/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O17 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-d61/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest temporal-difference-engine-is-native-axiom-free-and-reusable
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'signed/scale
             'learning/signed-td-error
             'learning/signed-q-update
             'learning/signed-q-iterate}
           (set (keys definitions))))
    (is (= #{'learning/signed-td-error-unfold
             'learning/signed-q-update-unfold
             'learning/signed-q-iterate-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-d61-q-learning-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-d61/theorem-ids checked-environment)]
    (is (= #{'ahof-d61/td-error-is-negative
             'ahof-d61/q-values
             'ahof-d61/q-learning}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-q-learning-corrects-overestimate-exactly
  ;; Overvalued estimate 1, reward 0, discount 0: TD error -1, Q converges to 0.
  (is (= -1 (executable/td-error 0 0 0 1)))
  (is (= [1 1/2 1/4 1/8]
         (executable/trajectory 1/2 0 0 0 1 3)))
  ;; A positive reward yields a positive correction.
  (is (= 1/2 (executable/q-update 1/2 1 0 0 0))))
