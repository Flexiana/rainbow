(ns rainbow.algorithms.proofs.conjugate-gradient-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.conjugate-gradient :as ahof-o18]
            [rainbow.algorithms.proofs.conjugate-gradient :as iteration]
            [rainbow.algorithms.reference.conjugate-gradient :as executable]
            [rainbow.algorithms.reference.momentum :as momentum]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o26-newton/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O26 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o18/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest conjugate-gradient-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/conjugate-direction 'optimization/conjugate-step
             'optimization/conjugate-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/conjugate-direction-unfold
             'optimization/conjugate-step-unfold
             'optimization/conjugate-iterate-zero}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o18-conjugate-gradient-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o18/theorem-ids checked-environment)]
    (is (= #{'ahof-o18/first-direction-is-negative-one
             'ahof-o18/first-position-is-three-halves
             'ahof-o18/conjugate-recurrence
             'ahof-o18/conjugate-gradient}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-conjugate-gradient-remembers-direction
  ;; alpha 1/2, beta 1, identity gradient, from [2 1]. New direction is
  ;; -grad(2) + 1*1 = -2 + 1 = -1 (the remembered direction 1 folded in), and
  ;; the position moves 2 + (1/2)(-1) = 3/2. Momentum at the same setup moves by
  ;; the full new direction, giving a different result.
  (let [g (fn [x] x)]
    (is (= -1 (executable/conjugate-direction 1 g 2 1)))
    (is (= [3/2 -1] (executable/step 1/2 1 g [2 1])))
    (is (not= (executable/step 1/2 1 g [2 1]) (momentum/step 1 1/2 g [2 1])))
    ;; Zero steps return the initial state.
    (is (= [2 1] (executable/run 1/2 1 g 0 [2 1])))))
