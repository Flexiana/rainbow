(ns rainbow.math.rational.nnrat.positive-monotone
  "B6c of the limit-reciprocal arc: positivity of an nnrat is preserved upward under <=.

    nat/positive-of-multiply-left : strict-below 0 (a*b) -> strict-below 0 a
    nnrat/positive-of-at-most      : positive p -> p <= q -> positive q

  Since nnrat/positive p reduces to strict-below 0 (numerator p) (== 1 <= num p), and
  strict-below 0 X == nat/at-most (succ 0) X, this is exactly the `1 <= num(mag(x*x))`
  hypothesis shape used across the arc. Proof of B6c: cross-multiply (at-most-to-cross),
  num p * den q is positive (multiply-right-strict-monotone-positive with left=0, using
  denominator-positive), chain <= to num q * den p (at-most-transitive), then factor-positive
  drops the den p factor. factor-positive itself is a Nat.rec on a: base a=0 is the identity
  (both sides are strict-below 0 0), step a=succ e gives the witness directly. Axiom-free;
  additive; does not touch the LP checker."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]
            [rainbow.math.rational.nnrat.positive :as positive]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private zero (function/const* 'data/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- sbelow [a b] (app (function/const* 'nat/strict-below []) a b))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denr [x] (app (function/const* 'nnrat/denominator []) x))
(defn- nnpos [p] (app (function/const* 'nnrat/positive []) p))
(defn- nn-le [p q] (app (function/const* 'nnrat/at-most []) p q))
(defn- eqn [x y] (function/equality tl nat x y))
(defn- refl-nat [x] (app (function/const* 'equality/reflexive [tl]) nat x))
(defn- nat-rec [motive base step n] (app (function/const* 'data/Nat.rec [[:zero]]) motive base step n))
(defn- witness [pred val proof] (app (function/const* 'proposition/witness [tl]) nat pred val proof))
(defn- to-cross [p q h] (app (function/const* 'nnrat/at-most-to-cross []) p q h))
(defn- den-pos [q] (app (function/const* 'nnrat/denominator-positive []) q))
(defn- mrsmp [factor left right ord fpos]
  (app (function/const* 'nat/multiply-right-strict-monotone-positive []) factor left right ord fpos))
(defn- nat-trans [a b c h1 h2] (app (function/const* 'nat/at-most-transitive []) a b c h1 h2))

;; factor-positive : strict-below 0 (a*b) -> strict-below 0 a
(def positive-of-multiply-left-spec
  {:name 'nat/positive-of-multiply-left
   :universes []
   :type (function/forall [['a nat] ['b nat] ['h (sbelow zero (nmul 'a 'b))]]
                          (sbelow zero 'a))
   :value
   (function/lam
    [['a nat] ['b nat] ['h (sbelow zero (nmul 'a 'b))]]
    (app
     (nat-rec
      (function/lam [['av nat]]
                    (function/arrow (sbelow zero (nmul 'av 'b)) (sbelow zero 'av)))
      ;; base a=0 : (strict-below 0 (0*b) == strict-below 0 0) -> strict-below 0 0  [identity]
      (function/lam [['h0 (sbelow zero (nmul zero 'b))]] 'h0)
      ;; step a=succ e : witness e, since add(succ 0) e = succ e
      (function/lam [['e nat] ['ih (function/arrow (sbelow zero (nmul 'e 'b)) (sbelow zero 'e))]]
                    (function/lam [['hs (sbelow zero (nmul (succ 'e) 'b))]]
                                  (witness (function/lam [['extra nat]]
                                                         (eqn (nadd (succ zero) 'extra) (succ 'e)))
                                           'e (refl-nat (succ 'e)))))
      'a)
     'h))})

(defn- factor-positive [a b h] (app (function/const* 'nat/positive-of-multiply-left []) a b h))

;; B6c : positive p -> p <= q -> positive q
(def positive-of-at-most-spec
  {:name 'nnrat/positive-of-at-most
   :universes []
   :type (function/forall [['p nnrat] ['q nnrat] ['hp (nnpos 'p)] ['hpq (nn-le 'p 'q)]]
                          (nnpos 'q))
   :value
   (function/lam
    [['p nnrat] ['q nnrat] ['hp (nnpos 'p)] ['hpq (nn-le 'p 'q)]]
    (let [cross (to-cross 'p 'q 'hpq)                                   ; num p*den q <= num q*den p
          ;; strict-below 0 (num p * den q)  [= mult 0 (den q) < mult (num p)(den q)]
          pd (mrsmp (denr 'q) zero (numr 'p) 'hp (den-pos 'q))
          ;; strict-below 0 (num q * den p)  via at-most-transitive (using sbelow 0 X == at-most 1 X)
          pq-pos (nat-trans (succ zero) (nmul (numr 'p) (denr 'q)) (nmul (numr 'q) (denr 'p)) pd cross)]
      (factor-positive (numr 'q) (denr 'p) pq-pos)))})

(def theorem-specs [positive-of-multiply-left-spec positive-of-at-most-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.positive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-positive-monotone theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.positive-monotone))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
