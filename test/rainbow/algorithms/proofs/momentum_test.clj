(ns rainbow.algorithms.proofs.momentum-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.momentum :as ahof-o19]
            [rainbow.algorithms.proofs.momentum :as iteration]
            [rainbow.algorithms.reference.momentum :as executable]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o12-bisection/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O12 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          iteration/extend-environment
          ahof-o19/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest momentum-engine-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (iteration/definition-ids checked-environment)
        theorems (iteration/theorem-ids checked-environment)]
    (is (= #{'optimization/momentum-velocity 'optimization/momentum-step
             'optimization/momentum-iterate}
           (set (keys definitions))))
    (is (= #{'optimization/momentum-velocity-unfold
             'optimization/momentum-step-unfold
             'optimization/momentum-iterate-zero
             'optimization/momentum-iterate-successor}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o19-momentum-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o19/theorem-ids checked-environment)]
    (is (= #{'ahof-o19/first-velocity-is-one
             'ahof-o19/first-position-is-one
             'ahof-o19/momentum-recurrence
             'ahof-o19/momentum}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-momentum-carries-velocity
  ;; beta 1, rate 1, unit gradient, from [0 2]: the momentum term 1*2=2 carries,
  ;; so v' = 2 - 1 = 1 and x' = 0 + 1 = 1 -- plain descent (no carry) would give
  ;; v' = -1, x' = -1.
  (let [g (fn [_x] 1)]
    (is (= [1 1] (executable/step 1 1 g [0 2])))
    (is (= [1 1] (executable/run 1 1 g 1 [0 2])))
    ;; Without the momentum carry (beta 0) the step is plain gradient descent.
    (is (= [-1 -1] (executable/step 0 1 g [0 2])))
    ;; Zero steps return the initial state.
    (is (= [0 2] (executable/run 1 1 g 0 [0 2])))))
