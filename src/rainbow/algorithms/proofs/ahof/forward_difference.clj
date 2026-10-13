(ns rainbow.algorithms.proofs.ahof.forward-difference
  "AHoF O1 Forward Difference: approximate a derivative by the forward finite difference
  (f(x+h) - f(x)) / h. With unit step h = 1 the estimate is the signed difference of the
  two evaluations:

      forward-difference f-plus f-base = f-plus - f-base   (over signed rationals).

  For f(x) = x^2 sampled at x = 1, h = 1: f(2) - f(1) = 4 - 1 = 3; a flat sample gives
  slope 0. Values are proved by signed cross-product equivalence. Proved native and
  axiom-free. Requires signed/subtract, signed/from-nnrat, signed/equivalent (all in the
  D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.forward-difference`
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
(defn- from-nnrat [v] (function/app (function/const* 'signed/from-nnrat []) v))
(defn- signed-of [n] (from-nnrat (whole-nnrat n)))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- signed-positive [v] (function/app (function/const* 'signed/positive []) v))
(defn- signed-negative [v] (function/app (function/const* 'signed/negative []) v))
(defn- signed-subtract [l r] (function/app (function/const* 'signed/subtract []) l r))
(defn- signed-equivalent [l r] (function/app (function/const* 'signed/equivalent []) l r))
(defn- signed-equivalent-cross [left right]
  (let [lhs (nnrat-add (signed-positive left) (signed-negative right))
        rhs (nnrat-add (signed-positive right) (signed-negative left))]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (multiply-nat (numerator lhs) (denominator rhs)))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- forward-difference [fp fb]
  (function/app (function/const* 'findiff/forward-difference []) fp fb))

(def forward-difference-spec
  {:name 'findiff/forward-difference :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam [['f-plus signed] ['f-base signed]]
                        (signed-subtract 'f-plus 'f-base))})

(def slope-example-spec
  {:name 'findiff/slope-example :kind :definition :universes [] :type signed
   :value (forward-difference (signed-of 4) (signed-of 1))})
(def flat-example-spec
  {:name 'findiff/flat-example :kind :definition :universes [] :type signed
   :value (forward-difference (signed-of 1) (signed-of 1))})

(def definition-specs [forward-difference-spec slope-example-spec flat-example-spec])

(def forward-difference-unfold-spec
  {:name 'findiff/forward-difference-unfold :universes []
   :type (function/forall [['f-plus signed] ['f-base signed]]
                          (equality signed (forward-difference 'f-plus 'f-base)
                                    (signed-subtract 'f-plus 'f-base)))
   :value (function/lam [['f-plus signed] ['f-base signed]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      signed (forward-difference 'f-plus 'f-base)))})

;; f(2) - f(1) = 4 - 1 = 3.
(def slope-is-three-spec
  {:name 'findiff/slope-is-three :universes []
   :type (signed-equivalent (function/const* 'findiff/slope-example []) (signed-of 3))
   :value (signed-equivalent-cross (function/const* 'findiff/slope-example []) (signed-of 3))})

;; A flat sample has slope 0.
(def flat-is-zero-spec
  {:name 'findiff/flat-is-zero :universes []
   :type (signed-equivalent (function/const* 'findiff/flat-example []) (signed-of 0))
   :value (signed-equivalent-cross (function/const* 'findiff/flat-example []) (signed-of 0))})

(def theorem-specs
  [forward-difference-unfold-spec slope-is-three-spec flat-is-zero-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-forward-difference (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.forward-difference))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
