(ns rainbow.algorithms.proofs.rmsprop
  "AHoF O22 RMSProp: the decayed squared-gradient accumulator that adapts the
  learning rate. Where AdaGrad (O21) sums all squared gradients, RMSProp keeps an
  exponentially-weighted average, retaining a fraction of the old accumulator and
  mixing in a fraction of the new squared gradient:

      accumulator' = retain * accumulator + fresh * gradient^2

  (with retain + fresh = 1). This is exact-rational multiplication and addition;
  the adaptive rate then divides a base rate by the square root of the
  accumulator, reusing the AdaGrad machinery. What is proved here is the decayed
  accumulator recurrence and a worked steady-state instance; the decay weights
  are supplied as concrete rationals.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.rmsprop`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))
(defn- numerator [value]
  (function/app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (function/app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (function/app (function/const* 'nat/multiply []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- accumulate [retain fresh prev grad-squared]
  (function/app (function/const* 'rmsprop/accumulate [])
                retain fresh prev grad-squared))

(defn- cross-product-reflexivity [left right]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator left) (denominator right))))

;; Definitions --------------------------------------------------------------

;; accumulator' = retain * prev + fresh * gradient^2
(def accumulate-spec
  {:name 'rmsprop/accumulate :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['retain nnrat] ['fresh nnrat]
                         ['prev nnrat] ['grad-squared nnrat]]
                        (add (multiply 'retain 'prev)
                             (multiply 'fresh 'grad-squared)))})

(def definition-specs [accumulate-spec])

;; Theorems -----------------------------------------------------------------

(def accumulate-unfold-spec
  {:name 'rmsprop/accumulate-unfold :universes []
   :type (function/forall
          [['retain nnrat] ['fresh nnrat] ['prev nnrat] ['grad-squared nnrat]]
          (equality nnrat (accumulate 'retain 'fresh 'prev 'grad-squared)
                    (add (multiply 'retain 'prev)
                         (multiply 'fresh 'grad-squared))))
   :value (function/lam [['retain nnrat] ['fresh nnrat] ['prev nnrat]
                         ['grad-squared nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (accumulate 'retain 'fresh 'prev 'grad-squared)))})

;; Steady state: retain 1/2, fresh 1/2, previous accumulator 4, squared gradient
;; 4 keeps the accumulator at 4 (1/2*4 + 1/2*4 = 4).
(def steady-state-example-spec
  {:name 'rmsprop/steady-state-example :universes []
   :type (equivalent (accumulate half half (whole 4) (whole 4)) (whole 4))
   :value (cross-product-reflexivity
           (accumulate half half (whole 4) (whole 4)) (whole 4))})

;; A rising accumulator: retain 1/2, fresh 1/2, previous 4, squared gradient 16
;; gives 1/2*4 + 1/2*16 = 10.
(def rising-example-spec
  {:name 'rmsprop/rising-example :universes []
   :type (equivalent (accumulate half half (whole 4) (whole 16)) (whole 10))
   :value (cross-product-reflexivity
           (accumulate half half (whole 4) (whole 16)) (whole 10))})

(def theorem-specs
  [accumulate-unfold-spec steady-state-example-spec rising-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :rmsprop (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.rmsprop))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
