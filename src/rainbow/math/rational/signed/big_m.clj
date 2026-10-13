(ns rainbow.math.rational.signed.big-m
  "Soundness of the indicator (\"big-M\") reformulation.

  A contract model says \"this activity may only run if we have committed to it\".
  An execution model cannot say that; it says

      x <= u * z,     z in {0, 1},

  where `u` is a bound the modeller believes the activity can never exceed. That
  substitution is the single most common place a linear model stops meaning what
  the business said, and it fails in two opposite directions:

    TOO TIGHT -- the row quietly forbids something the contract allowed, so the
    solver returns a worse plan than the business could have run and nobody can
    tell, because the model is still feasible;

    NOT BINDING -- the row fails to force the activity off, so the plan violates
    the commitment it was supposed to encode.

  The two theorems here are exactly those two directions:

    optimization/big-m-row-inactive : x <= u  ->  x <= u * 1
      committing to the activity cannot cut off anything the bound already
      allowed, so the encoding is not too tight;

    optimization/big-m-forces-zero : x <= u * z  ->  z ~ 0  ->  x <= 0
      declining the activity does force the quantity to zero, so the encoding
      binds.

  Both are stated over signed rationals, so `u` may be negative and `z` is an
  ordinary value rather than a special-cased flag. Neither theorem assumes `u` is
  a VALID bound -- that is a modelling claim about the business, and it stays the
  modeller's to make. What is proved is that GIVEN the bound, the row means what
  the contract said.

  Native and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as ring]))

(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def signed-one (function/const* 'signed/one []))

(defn- app [f & args] (apply function/app f args))
(defn- pos [v] (app (function/const* 'signed/positive []) v))
(defn- neg [v] (app (function/const* 'signed/negative []) v))
(defn- radd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- seq-equiv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn- rat-sym [a b same]
  (app (function/const* 'nnrat/equivalent-symmetric []) a b same))
;; signed equivalence IS the nnrat equivalence of the two cross sums
(defn- signed-sym [a b same]
  (rat-sym (radd (pos a) (neg b)) (radd (pos b) (neg a)) same))
(defn- signed-refl [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-trans [a b c ab bc]
  (app (function/const* 'signed/equivalent-transitive []) a b c ab bc))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))
(defn- multiply-commutative [a b]
  (app (function/const* 'signed/multiply-commutative []) a b))
(defn- multiply-one-left [v]
  (app (function/const* 'signed/multiply-one-left []) v))
(defn- multiply-zero-right [v]
  (app (function/const* 'signed/multiply-zero-right []) v))
(defn- multiply-left-respects [b bh c same]
  (app (function/const* 'signed/multiply-left-respects-equivalence [])
       b bh c same))

;; u * 1 ~ u, by commuting and then the unit law
(defn- times-one [u]
  (signed-trans (smul u signed-one) (smul signed-one u) u
                (multiply-commutative u signed-one)
                (multiply-one-left u)))

(def row-inactive-spec
  {:name 'optimization/big-m-row-inactive :universes []
   :type (function/forall
          [['x signed] ['u signed]
           ['bounded (sle 'x 'u)]]
          (sle 'x (smul 'u signed-one)))
   :value
   (function/lam
    [['x signed] ['u signed]
     ['bounded (sle 'x 'u)]]
    (signed-at-most-respects
     'x 'x 'u (smul 'u signed-one)
     (signed-refl 'x)
     (signed-sym (smul 'u signed-one) 'u (times-one 'u))
     'bounded))})

(def forces-zero-spec
  {:name 'optimization/big-m-forces-zero :universes []
   :type (function/forall
          [['x signed] ['u signed] ['z signed]
           ['indicated (sle 'x (smul 'u 'z))]
           ['declined (seq-equiv 'z signed-zero)]]
          (sle 'x signed-zero))
   :value
   (function/lam
    [['x signed] ['u signed] ['z signed]
     ['indicated (sle 'x (smul 'u 'z))]
     ['declined (seq-equiv 'z signed-zero)]]
    (signed-at-most-respects
     'x 'x (smul 'u 'z) signed-zero
     (signed-refl 'x)
     (signed-trans (smul 'u 'z) (smul 'u signed-zero) signed-zero
                   (multiply-left-respects 'z signed-zero 'u 'declined)
                   (multiply-zero-right 'u))
     'indicated))})

(def definition-specs [])
(def theorem-specs [row-inactive-spec forces-zero-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ring/extend-environment
      (support/extend-with :signed-big-m theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
