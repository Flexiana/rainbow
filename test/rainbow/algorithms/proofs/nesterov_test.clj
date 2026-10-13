(ns rainbow.algorithms.proofs.nesterov-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.nesterov :as ahof-o20]
            [rainbow.algorithms.proofs.nesterov :as iteration]
            [rainbow.algorithms.reference.nesterov :as executable]
            [rainbow.algorithms.reference.momentum :as momentum]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o13-general-descent/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O13 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o20/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest nesterov-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/nesterov-lookahead 'optimization/nesterov-velocity
             'optimization/nesterov-step 'optimization/nesterov-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/nesterov-lookahead-unfold
             'optimization/nesterov-velocity-unfold
             'optimization/nesterov-step-unfold
             'optimization/nesterov-iterate-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o20-nesterov-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o20/theorem-ids checked-environment)]
    (is (= #{'ahof-o20/first-velocity-is-negative-one
             'ahof-o20/first-position-is-zero
             'ahof-o20/nesterov-recurrence
             'ahof-o20/nesterov}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-nesterov-lookahead-differs-from-momentum
  ;; beta 1, rate 1, position-dependent gradient (positive part), from [1 1].
  ;; Nesterov evaluates the gradient at the look-ahead point 1 + 1*1 = 2, so
  ;; grad = 2 and v' = 1 - 2 = -1, x' = 0. Momentum uses grad at x = 1, so
  ;; v' = 0, x' = 1. The look-ahead genuinely changes the trajectory.
  (let [g (fn [point] (max 0 point))]
    (is (= 2 (executable/lookahead 1 1 1)))
    (is (= [0 -1] (executable/step 1 1 g [1 1])))
    (is (= [1 0] (momentum/step 1 1 g [1 1])))
    (is (not= (executable/step 1 1 g [1 1]) (momentum/step 1 1 g [1 1])))
    ;; Zero steps return the initial state.
    (is (= [1 1] (executable/run 1 1 g 0 [1 1])))))
