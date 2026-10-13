(ns rainbow.algorithms.proofs.ahof.complex-step
  "AHoF O3 Complex-Step Derivative (classical method: f'(x) ~ Im f(x + ih) / h, which
  avoids subtractive cancellation). This module does NOT model it: it has no complex
  numbers, no imaginary part, no perturbation and no step size. What is defined and proved
  is plain signed subtraction of two supplied values:
  derivative-estimate a b = a - b, unfolding to signed/subtract for all signed inputs (by
  reflexivity), with worked instances 4-1 = 3 (slope-example-is-3) and 2-2 = 0
  (flat-example-is-0). Complex-step differentiation itself is classical and not proved here.
  Values proved by signed cross-product equivalence. Proved native and axiom-free.
  Requires signed/subtract, signed/from-nnrat, signed/equivalent (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.complex-step`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole-nnrat [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- signed-of [n] (function/app (function/const* 'signed/from-nnrat []) (whole-nnrat n)))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- signed-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- signed-op [l r] (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-equivalent [l r] (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'complex-step/derivative-estimate []) a b))

(def op-spec
  {:name 'complex-step/derivative-estimate :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-op 'a 'b))})

(def slope-example-spec
  {:name 'complex-step/slope-example :kind :definition :universes [] :type signed
   :value (op (signed-of 4) (signed-of 1))})

(def flat-example-spec
  {:name 'complex-step/flat-example :kind :definition :universes [] :type signed
   :value (op (signed-of 2) (signed-of 2))})

(def definition-specs [op-spec slope-example-spec flat-example-spec])

(def op-unfold-spec
  {:name 'complex-step/derivative-estimate-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-op 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def slope-example-is-3-spec
  {:name 'complex-step/slope-example-is-3 :universes []
   :type (signed-equivalent (function/const* 'complex-step/slope-example []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'complex-step/slope-example []) (signed-of 3))})

(def flat-example-is-0-spec
  {:name 'complex-step/flat-example-is-0 :universes []
   :type (signed-equivalent (function/const* 'complex-step/flat-example []) (signed-of 0))
   :value (signed-equivalent-cross (function/const* 'complex-step/flat-example []) (signed-of 0))})

(def theorem-specs [op-unfold-spec slope-example-is-3-spec flat-example-is-0-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-complex-step
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
