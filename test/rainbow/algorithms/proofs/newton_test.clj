(ns rainbow.algorithms.proofs.newton-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.newton :as ahof-o26]
            [rainbow.algorithms.proofs.newton :as newton]
            [rainbow.math.rational.division :as division]
            [rainbow.algorithms.reference.newton :as executable]
            [rainbow.algorithms.reference.general-descent :as general]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o32-coordinate-search/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O32 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          division/extend-environment
          newton/extend-environment
          ahof-o26/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest newton-rate-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (newton/definition-ids checked-environment)
        theorems (newton/theorem-ids checked-environment)]
    (is (= #{'optimization/newton-rate} (set (keys definitions))))
    (is (= #{'optimization/newton-rate-unfold} (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o26-newton-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o26/theorem-ids checked-environment)]
    (is (= #{'ahof-o26/reaches-minimum-in-one-step
             'ahof-o26/newton-recurrence
             'ahof-o26/newton}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-newton-reaches-quadratic-minimum-in-one-step
  ;; f(x) = x^2: Hessian 2, gradient 2x, step size 1/2. From x = 2 one Newton
  ;; step is 2 - (1/2)(2*2) = 0 -- the minimum, in a single step. Fixed-rate
  ;; gradient descent at the same rate takes infinitely many steps to reach it.
  (let [hessian (fn [_x] 2)
        gradient (fn [x] (* 2 x))]
    (is (= 1/2 (executable/rate hessian 2)))
    (is (= 0 (executable/step hessian gradient 2)))
    (is (= 0 (executable/run hessian gradient 1 2)))
    ;; Newton is the general descent skeleton with a Hessian-inverse step size.
    (is (= 0 (general/step gradient
                           (fn [x] (executable/rate hessian x))
                           (fn [point rate dir] (- point (* rate dir)))
                           2)))))
