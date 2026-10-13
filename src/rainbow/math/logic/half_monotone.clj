(ns rainbow.math.logic.half-monotone
  "The general halving-monotonicity lemma for the convergence capstone:

      (1/2) * d  <=  d     for every nonnegative rational d.

  Worked instances live in geometric-convergence; this is the abstract-d step
  the general `forall epsilon` convergence theorem needs. The proof is by
  transport, not reflexivity, because `nnrat/multiply` stores the numerator as a
  nat product and the denominator via `combine-denominator-predecessors`, and
  because `algebra/nat-add` recurses on its LEFT argument -- so `x + 0` does NOT
  reduce to `x` definitionally (`algebra/nat-add-zero-right` is a theorem, not a
  reduction). Concretely, for half = 1/1 the projections reduce to

      numerator   ((1/2)*d)  ==  (num d) + 0
      denominator ((1/2)*d)  ==  (den d) + ((den d) + 0)

  so `nnrat/base-at-most ((1/2)*d) d` normalizes to

      (num d)*(den d)  <=  (num d)*((den d)+(den d))

  once the two `+ 0` remainders are rewritten away. That inequality is
  `nat/multiply-left-monotone` applied to `nat/le-add-self (den d)`
  (den d <= den d + den d); the two `algebra/nat-add-zero-right` rewrites are
  transported through the cross terms with `equality/substitution` and
  `equality/congruent-function`, and `nnrat/at-most-from-cross` lifts the cross
  bound to the native `nnrat/at-most`.

  Requires nnrat/multiply, nnrat/half, nnrat/at-most-from-cross,
  nat/multiply-left-monotone, nat/le-add-self, algebra/nat-add-zero-right,
  equality/substitution, and equality/congruent-function."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))

(defn- mul [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-at-most [l r] (function/app (function/const* 'nat/at-most []) l r))
(defn- nnrat-at-most [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(def zero (function/const* 'data/zero []))

(defn- le-add-self [x]
  (function/app (function/const* 'nat/le-add-self []) x))
(defn- multiply-left-monotone [factor left right ordered]
  (function/app (function/const* 'nat/multiply-left-monotone [])
                factor left right ordered))
(defn- at-most-from-cross [left right ordered]
  (function/app (function/const* 'nnrat/at-most-from-cross [])
                left right ordered))
(defn- nat-add-zero-right [x]
  (function/app (function/const* 'algebra/nat-add-zero-right []) x))
(defn- congruent [f x y h]
  (function/app (function/const* 'equality/congruent-function
                                 [type-level type-level])
                nat nat f x y h))
(defn- symmetric [x y h]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat x y h))
(defn- substitute [x y h motive px]
  (function/app (function/const* 'equality/substitution [type-level])
                nat x y h motive px))

;; ((1/2) * d) <= d  for every nonnegative rational d.
(def half-le-self-spec
  {:name 'nnrat/half-le-self :universes []
   :type (function/forall [['d nnrat]]
                          (nnrat-at-most (nnrat-multiply half 'd) 'd))
   :value
   (function/lam
    [['d nnrat]]
    (let [half-d (nnrat-multiply half 'd)
          nd (numerator 'd)
          dd (denominator 'd)
          num-hd (numerator half-d)     ; definitionally  (add nd zero)
          den-hd (denominator half-d)   ; definitionally  (add dd (add dd zero))
          double-dd (add dd dd)
          left-a (mul nd dd)            ; P's left endpoint
          left-ap (mul num-hd dd)       ; base-at-most's left endpoint
          right-b (mul nd double-dd)    ; P's right endpoint
          right-bp (mul nd den-hd)      ; base-at-most's right endpoint
          ;; P : nat-at-most (mul nd dd) (mul nd (add dd dd))
          p (multiply-left-monotone nd dd double-dd (le-add-self dd))
          ;; den-hd = add dd dd     (rewrite the inner `+ 0`)
          e-den (congruent (function/lam [['v nat]] (add dd 'v))
                           (add dd zero) dd (nat-add-zero-right dd))
          ;; right-bp = right-b, then reverse to right-b = right-bp
          e-right (congruent (function/lam [['v nat]] (mul nd 'v))
                             den-hd double-dd e-den)
          e-right-sym (symmetric right-bp right-b e-right)
          ;; step1 : nat-at-most (mul nd dd) right-bp
          step1 (substitute right-b right-bp e-right-sym
                            (function/lam [['b nat]] (nat-at-most left-a 'b))
                            p)
          ;; num-hd = nd    (rewrite the `+ 0`)
          e-num (nat-add-zero-right nd)
          ;; left-ap = left-a, then reverse to left-a = left-ap
          e-left (congruent (function/lam [['v nat]] (mul 'v dd))
                            num-hd nd e-num)
          e-left-sym (symmetric left-ap left-a e-left)
          ;; step2 : nat-at-most left-ap right-bp  ==  base-at-most half-d d
          step2 (substitute left-a left-ap e-left-sym
                            (function/lam [['a nat]] (nat-at-most 'a right-bp))
                            step1)]
      (at-most-from-cross half-d 'd step2)))})

(def definition-specs [])
(def theorem-specs [half-le-self-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :half-monotone theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.logic.half-monotone))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
