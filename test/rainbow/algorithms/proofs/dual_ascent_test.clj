(ns rainbow.algorithms.proofs.dual-ascent-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.vector :as vector]
            [rainbow.algorithms.proofs.dual-ascent :as dual-ascent]
            [rainbow.algorithms.reference.dual-ascent :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "D63 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          vector/extend-environment
          dual-ascent/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest dual-ascent-step-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (dual-ascent/definition-ids checked-environment)
        theorems (dual-ascent/theorem-ids checked-environment)]
    (is (= #{'dual-ascent/ascent-step} (set (keys definitions))))
    (is (= #{'dual-ascent/ascent-unfold
             'dual-ascent/unit-step-2d-example
             'dual-ascent/unit-step-3d-example}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-dual-ascent-matches-the-recurrence
  ;; From a zero multiplier a unit-rate step lands on the residual, and a
  ;; constant residual accumulates linearly over the iteration.
  (is (= [3 2] (executable/ascent-step [0 0] [3 2] 1)))
  (is (= [6 4] (executable/iterate-dual (constantly [3 2]) [0 0] 1 2)))
  (is (= [0 0] (executable/iterate-dual (constantly [3 2]) [0 0] 1 0))))
