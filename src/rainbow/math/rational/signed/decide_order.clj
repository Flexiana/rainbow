(ns rainbow.math.rational.signed.decide-order
  "A DECIDABLE signed-rational order -- the per-instance half of a certificate.

  The optimality theorems in `rainbow.math.rational.signed.lp-duality` are parametric:
  they hold for every matrix, cost vector and dual vector. Applying one to an
  actual customer instance means discharging its hypotheses -- primal
  feasibility, dual feasibility, nonnegativity -- for actual numbers. Without a
  decision procedure each of those inequalities needs a hand-built proof, which
  is why the parametric theorems, on their own, do not yet check anything.

    signed/decide-at-most             : signed -> signed -> Bool   (computable)
    signed/decide-at-most-true-sound  : decide a b = true  -> a <= b
    signed/decide-at-most-false-reverse : decide a b = false -> b <= a

  With these, a concrete inequality is discharged by REDUCTION: the decision
  computes to `true`, `equality/reflexive` proves that it did, and soundness
  turns it into the order fact the theorem wants. That is the shape a checker
  needs -- expensive parametric proof once, cheap arithmetic per instance.

  The bridge is definitional rather than earned. Signed order `a <= b` unfolds
  to the nnrat comparison `positive a + negative b <= positive b + negative a`,
  so the existing decidable nnrat order applied to those two cross sums IS the
  decision procedure, and the existing nnrat soundness lemmas applied to the same
  two terms ARE its soundness proofs. Nothing new is assumed and the trusted base
  is unchanged.

  Native and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))

(defn- decide-nnrat [l r]
  (app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- decide-signed [a b]
  (app (function/const* 'signed/decide-at-most []) a b))

;; the two cross sums signed order unfolds to
(defn- forward [a b] (radd (pos a) (neg b)))
(defn- backward [a b] (radd (pos b) (neg a)))

(def decide-at-most-spec
  {:name 'signed/decide-at-most :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed bool)
   :value (function/lam
           [['left signed] ['right signed]]
           (decide-nnrat (forward 'left 'right) (backward 'left 'right)))})

(def decide-at-most-true-sound-spec
  {:name 'signed/decide-at-most-true-sound :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['decided (eq-bool (decide-signed 'a 'b) true-value)]]
          (sle 'a 'b))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['decided (eq-bool (decide-signed 'a 'b) true-value)]]
    (app (function/const* 'nnrat/decide-at-most-true-sound [])
         (forward 'a 'b) (backward 'a 'b) 'decided))})

(def decide-at-most-false-reverse-spec
  {:name 'signed/decide-at-most-false-reverse :universes []
   :type (function/forall
          [['a signed] ['b signed]
           ['decided (eq-bool (decide-signed 'a 'b) false-value)]]
          (sle 'b 'a))
   :value
   (function/lam
    [['a signed] ['b signed]
     ['decided (eq-bool (decide-signed 'a 'b) false-value)]]
    (app (function/const* 'nnrat/decide-at-most-false-reverse [])
         (forward 'a 'b) (backward 'a 'b) 'decided))})

(def definition-specs [decide-at-most-spec])
(def theorem-specs
  [decide-at-most-true-sound-spec decide-at-most-false-reverse-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :signed-decide-order
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
