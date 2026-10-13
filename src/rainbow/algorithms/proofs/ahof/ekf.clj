(ns rainbow.algorithms.proofs.ahof.ekf
  "AHoF D68 Extended Kalman Filter: the EKF linearizes the nonlinear process and
  measurement models about the current estimate and applies the standard Kalman
  measurement update, blending the prediction with the observation by the Kalman gain:

      update wp prior wm measurement = wp * prior + wm * measurement

  (with wp + wm = 1 the complementary predict/measurement weights). Blending a
  prediction 1/2 and a measurement 3/4 with equal weights gives 5/8; trusting the
  measurement fully (weights 0, 1) gives 3/4. Values are proved by cross-product
  equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ekf`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def half (make-rational 1 1))            ; 1/2
(def three-quarters (make-rational 3 3))  ; 3/4
(def five-eighths (make-rational 5 7))    ; 5/8

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- update [wp prior wm measurement]
  (function/app (function/const* 'ekf/update []) wp prior wm measurement))

(def update-spec
  {:name 'ekf/update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['wp nnrat] ['prior nnrat] ['wm nnrat] ['measurement nnrat]]
                        (nnrat-add (nnrat-multiply 'wp 'prior)
                                   (nnrat-multiply 'wm 'measurement)))})

(def balanced-update-spec
  {:name 'ekf/balanced-update :kind :definition :universes [] :type nnrat
   :value (update half half half three-quarters)})
(def measurement-trusting-update-spec
  {:name 'ekf/measurement-trusting-update :kind :definition :universes [] :type nnrat
   :value (update nnrat-zero half nnrat-one three-quarters)})

(def definition-specs
  [update-spec balanced-update-spec measurement-trusting-update-spec])

(def update-unfold-spec
  {:name 'ekf/update-unfold :universes []
   :type (function/forall [['wp nnrat] ['prior nnrat] ['wm nnrat] ['measurement nnrat]]
                          (equality nnrat (update 'wp 'prior 'wm 'measurement)
                                    (nnrat-add (nnrat-multiply 'wp 'prior)
                                               (nnrat-multiply 'wm 'measurement))))
   :value (function/lam [['wp nnrat] ['prior nnrat] ['wm nnrat] ['measurement nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (update 'wp 'prior 'wm 'measurement)))})

;; Equal-weight blend of prediction 1/2 and measurement 3/4 is 5/8.
(def balanced-is-five-eighths-spec
  {:name 'ekf/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'ekf/balanced-update []) five-eighths)
   :value (equivalent-cross (function/const* 'ekf/balanced-update []) five-eighths)})

;; Fully trusting the measurement returns the measurement 3/4.
(def trusting-is-measurement-spec
  {:name 'ekf/trusting-is-measurement :universes []
   :type (nnrat-equivalent (function/const* 'ekf/measurement-trusting-update []) three-quarters)
   :value (equivalent-cross (function/const* 'ekf/measurement-trusting-update []) three-quarters)})

(def ekf-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type trusting-is-measurement-spec)]
    {:name 'ekf/ekf :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'ekf/balanced-is-five-eighths [])
                          (function/const* 'ekf/trusting-is-measurement []))}))

(def theorem-specs
  [update-unfold-spec balanced-is-five-eighths-spec trusting-is-measurement-spec
   ekf-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-ekf (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.ekf))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
