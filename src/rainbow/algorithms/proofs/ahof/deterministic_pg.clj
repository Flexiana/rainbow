(ns rainbow.algorithms.proofs.ahof.deterministic-pg
  "AHoF D55 Deterministic Policy Gradient: the DPG theorem gives the gradient as the\n  chain product of the action-value gradient and the policy Jacobian, grad =\n  \u2207_a Q \u00b7 \u2207_\u03b8 \u03bc: policy-gradient q-grad mu-grad = q-grad * mu-grad (over signed).\n  Worked: 2 * 3 = 6.
  Values proved by signed cross-product equivalence. Proved native and axiom-free.
  Requires signed/multiply (from rainbow.math.rational.signed.multiply, chained), signed/from-nnrat,
  signed/equivalent.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.deterministic-pg`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.signed.multiply :as signed-multiply]))

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
(defn- signed-multiply [l r] (function/app (function/const* 'signed/multiply []) l r))
(defn- signed-equivalent [l r] (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [a b] (function/app (function/const* 'det-pg/policy-gradient []) a b))

(def op-spec
  {:name 'det-pg/policy-gradient :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-multiply 'a 'b))})

(def gradient-example-spec
  {:name 'det-pg/gradient-example :kind :definition :universes [] :type signed
   :value (op (signed-of 2) (signed-of 3))})

(def unit-jacobian-spec
  {:name 'det-pg/unit-jacobian :kind :definition :universes [] :type signed
   :value (op (signed-of 3) (signed-of 1))})

(def definition-specs [op-spec gradient-example-spec unit-jacobian-spec])

(def op-unfold-spec
  {:name 'det-pg/policy-gradient-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-multiply 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def gradient-example-is-6-spec
  {:name 'det-pg/gradient-example-is-6 :universes []
   :type (signed-equivalent (function/const* 'det-pg/gradient-example []) (signed-of 6))
   :value (signed-equivalent-cross (function/const* 'det-pg/gradient-example []) (signed-of 6))})

(def unit-jacobian-is-3-spec
  {:name 'det-pg/unit-jacobian-is-3 :universes []
   :type (signed-equivalent (function/const* 'det-pg/unit-jacobian []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'det-pg/unit-jacobian []) (signed-of 3))})

(def theorem-specs [op-unfold-spec gradient-example-is-6-spec unit-jacobian-is-3-spec])

;; installs signed/multiply, which these specs use, so the module installs on any base
(defn extend-environment [checked-environment]
  (support/extend-with (signed-multiply/extend-environment checked-environment) :ahof-deterministic-pg
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
