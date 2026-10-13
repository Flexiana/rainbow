(ns rainbow.algorithms.proofs.ahof.forward-mode-ad
  "AHoF O4 Forward-Mode Auto-Diff: propagate derivatives through a computation with dual\n  numbers; the chain rule composes derivatives multiplicatively (f\u2218g)'=f'(g)\u00b7g':\n  dual-derivative outer-deriv inner-deriv = outer-deriv * inner-deriv (over signed).\n  Worked: 2 * 3 = 6.
  Values proved by signed cross-product equivalence. Proved native and axiom-free.
  Requires signed/multiply (from rainbow.math.rational.signed.multiply, chained), signed/from-nnrat,
  signed/equivalent.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.forward-mode-ad`
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

(defn- op [a b] (function/app (function/const* 'fwd-ad/dual-derivative []) a b))

(def op-spec
  {:name 'fwd-ad/dual-derivative :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['a signed] ['b signed]] (signed-multiply 'a 'b))})

(def chain-example-spec
  {:name 'fwd-ad/chain-example :kind :definition :universes [] :type signed
   :value (op (signed-of 2) (signed-of 3))})

(def identity-inner-spec
  {:name 'fwd-ad/identity-inner :kind :definition :universes [] :type signed
   :value (op (signed-of 3) (signed-of 1))})

(def definition-specs [op-spec chain-example-spec identity-inner-spec])

(def op-unfold-spec
  {:name 'fwd-ad/dual-derivative-unfold :universes []
   :type (function/forall [['a signed] ['b signed]]
                          (equality signed (op 'a 'b) (signed-multiply 'a 'b)))
   :value (function/lam [['a signed] ['b signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (op 'a 'b)))})

(def chain-example-is-6-spec
  {:name 'fwd-ad/chain-example-is-6 :universes []
   :type (signed-equivalent (function/const* 'fwd-ad/chain-example []) (signed-of 6))
   :value (signed-equivalent-cross (function/const* 'fwd-ad/chain-example []) (signed-of 6))})

(def identity-inner-is-3-spec
  {:name 'fwd-ad/identity-inner-is-3 :universes []
   :type (signed-equivalent (function/const* 'fwd-ad/identity-inner []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'fwd-ad/identity-inner []) (signed-of 3))})

(def theorem-specs [op-unfold-spec chain-example-is-6-spec identity-inner-is-3-spec])

;; installs signed/multiply, which these specs use, so the module installs on any base
(defn extend-environment [checked-environment]
  (support/extend-with (signed-multiply/extend-environment checked-environment) :ahof-forward-mode-ad
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
