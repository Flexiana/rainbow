(ns rainbow.math.nat.add-order
  "Additive monotonicity building blocks for the convergence proof: a natural
  number is at most itself plus anything, and in particular at most its own
  double. `nat/at-most a b` unfolds to the existence of a witness `extra` with
  `a + extra = b`, so these follow directly by supplying the witness and
  reflexivity -- no induction. They feed the nnrat multiplication-monotonicity
  step `(1/2)*d <= d` and thence the geometric-sequence monotonicity in the
  convergence development.

  Requires `nat/at-most`, `algebra/nat-add`, and `proposition/witness`."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- equality [l r] (function/equality type-level nat l r))
(defn- at-most [l r] (function/app (function/const* 'nat/at-most []) l r))

;; A proof of `nat/at-most left right` from a witness `extra` with a proof that
;; `left + extra = right` (matching the existential definition of nat/at-most).
(defn- at-most-witness [left right extra evidence]
  (function/app
   (function/const* 'proposition/witness [type-level])
   nat
   (function/lam [['w nat]] (equality (add left 'w) right))
   extra evidence))

;; Theorems -----------------------------------------------------------------

;; x <= x + y  (a number is at most itself plus anything): witness y, since
;; x + y = x + y by reflexivity.
(def le-add-right-spec
  {:name 'nat/le-add-right :universes []
   :type (function/forall [['x nat] ['y nat]] (at-most 'x (add 'x 'y)))
   :value (function/lam
           [['x nat] ['y nat]]
           (at-most-witness 'x (add 'x 'y) 'y
                            (function/app
                             (function/const* 'equality/reflexive [type-level])
                             nat (add 'x 'y))))})

;; x <= x + x  (a number is at most its own double): the y = x case.
(def le-add-self-spec
  {:name 'nat/le-add-self :universes []
   :type (function/forall [['x nat]] (at-most 'x (add 'x 'x)))
   :value (function/lam
           [['x nat]]
           (at-most-witness 'x (add 'x 'x) 'x
                            (function/app
                             (function/const* 'equality/reflexive [type-level])
                             nat (add 'x 'x))))})

(def definition-specs [])
(def theorem-specs [le-add-right-spec le-add-self-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nat-add-order theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.add-order))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
