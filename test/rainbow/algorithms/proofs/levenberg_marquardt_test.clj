(ns rainbow.algorithms.proofs.levenberg-marquardt-test
  (:require [clojure.test :refer [deftest is]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.ahof.levenberg-marquardt :as ahof-o31]
            [rainbow.algorithms.proofs.levenberg-marquardt :as lm]
            [rainbow.math.rational.division :as division]
            [rainbow.algorithms.reference.levenberg-marquardt :as executable]
            [rainbow.algorithms.reference.newton :as newton]))

(def checked-environment
  (delay
    (let [checkpoint
          (checkpoint/load-checkpoint
           "artifacts/ahof/o18-conjugate-gradient/checkpoint.edn.gz")]
      (when-not (= :replayed (:status checkpoint))
        (throw (ex-info "O18 checkpoint rejected" {:checkpoint checkpoint})))
      (-> (:environment checkpoint)
          division/extend-environment
          lm/extend-environment
          ahof-o31/extend-environment))))

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(deftest lm-rate-is-native-axiom-free
  (let [checked-environment @checked-environment
        definitions (lm/definition-ids checked-environment)
        theorems (lm/theorem-ids checked-environment)]
    (is (= #{'optimization/levenberg-marquardt-rate} (set (keys definitions))))
    (is (= #{'optimization/levenberg-marquardt-rate-unfold}
           (set (keys theorems))))
    (doseq [[name id] (concat definitions theorems)]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest worked-o31-levenberg-marquardt-is-kernel-checked-and-axiom-free
  (let [checked-environment @checked-environment
        theorems (ahof-o31/theorem-ids checked-environment)]
    (is (= #{'ahof-o31/damped-step-is-one
             'ahof-o31/levenberg-marquardt-recurrence
             'ahof-o31/levenberg-marquardt}
           (set (keys theorems))))
    (doseq [[name id] theorems]
      (is (= #{} (kernel/axioms checked-environment id)) (str name))
      (is (checked? checked-environment id) (str name)))))

(deftest executable-lm-damps-the-newton-step
  ;; f(x) = x^2: Hessian 2, gradient 2x. Newton (lambda 0) leaps from 2 to 0.
  ;; Levenberg-Marquardt with damping 2 has step size 1/(2+2) = 1/4, so the step
  ;; from 2 is 2 - (1/4)(2*2) = 1 -- a shorter, damped step.
  (let [hessian (fn [_x] 2)
        gradient (fn [x] (* 2 x))]
    (is (= 1/4 (executable/rate hessian 2 2)))
    (is (= 1 (executable/step hessian 2 gradient 2)))
    (is (= 1 (executable/run hessian 2 gradient 1 2)))
    ;; Newton (lambda 0) leaps to the minimum; LM damps it.
    (is (= 0 (newton/run hessian gradient 1 2)))
    (is (not= (executable/run hessian 2 gradient 1 2)
              (newton/run hessian gradient 1 2)))))
