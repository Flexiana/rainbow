(ns rainbow.algorithms.proofs.ahof.central-difference
  "AHoF O2 Central Difference: the central finite difference estimates a derivative as
  (f(x+h) - f(x-h)) / (2h). What is defined here is only its NUMERATOR, the signed
  difference of the two evaluations: central-difference f-plus f-minus = f-plus - f-minus;
  the division by 2h is not performed. For f(x)=x^2 at x=1, h=1 the proved numerator is
  f(2)-f(0) = 4-0 = 4 (slope-example-is-4); the divided estimate would be 4/(2*1) = 2,
  which is not computed or proved here. Also proved: the symmetric pair 2-2 = 0
  (symmetric-flat-is-0), and that central-difference unfolds to signed/subtract for all
  signed inputs (by reflexivity). Values proved by signed cross-product equivalence.
  Proved native and axiom-free.
  Requires signed/subtract, signed/from-nnrat, signed/equivalent (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.central-difference`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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

(defn- op [a b] (function/app (function/const* 'central-diff/central-difference []) a b))

(def op-spec
  {:name 'central-diff/central-difference :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-op 'a 'b))})

(def slope-example-spec
  {:name 'central-diff/slope-example :kind :definition :universes [] :type signed
   :value (op (signed-of 4) (signed-of 0))})

(def symmetric-flat-spec
  {:name 'central-diff/symmetric-flat :kind :definition :universes [] :type signed
   :value (op (signed-of 2) (signed-of 2))})

(def definition-specs [op-spec slope-example-spec symmetric-flat-spec])

(def op-unfold-spec
  {:name 'central-diff/central-difference-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-op 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def slope-example-is-4-spec
  {:name 'central-diff/slope-example-is-4 :universes []
   :type (signed-equivalent (function/const* 'central-diff/slope-example []) (signed-of 4))
   :value (signed-equivalent-cross (function/const* 'central-diff/slope-example []) (signed-of 4))})

(def symmetric-flat-is-0-spec
  {:name 'central-diff/symmetric-flat-is-0 :universes []
   :type (signed-equivalent (function/const* 'central-diff/symmetric-flat []) (signed-of 0))
   :value (signed-equivalent-cross (function/const* 'central-diff/symmetric-flat []) (signed-of 0))})

(def theorem-specs [op-unfold-spec slope-example-is-4-spec symmetric-flat-is-0-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-central-difference (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.central-difference))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
