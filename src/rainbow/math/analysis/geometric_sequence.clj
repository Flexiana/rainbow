(ns rainbow.math.analysis.geometric-sequence
  "The geometric contraction sequence as a native recursive function and its
  general (forall-n) step monotonicity -- the sequence-level consequence of the
  halving-monotonicity keystone (nnrat/half-le-self). For a starting distance d0
  the sequence

      seq d0 0        = d0
      seq d0 (succ n) = (1/2) * (seq d0 n)         (= (1/2)^n * d0)

  is defined by recursion on n (data/Nat.rec). Its step monotonicity

      seq d0 (succ n)  <=  seq d0 n      for every n

  is exactly nnrat/half-le-self instantiated at the term (seq d0 n): the next
  distance is half the current one, hence no larger. This is the general
  monotone-decrease of the contraction distances (the worked instances live in
  geometric-convergence), one of the two ingredients -- with a modulus that
  drives the distance below any threshold -- of the forall-epsilon convergence
  theorem convergence/converges-to.

  Requires nnrat/multiply, nnrat/half, nnrat/at-most, and nnrat/half-le-self."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def half (function/const* 'nnrat/half []))
(def successor (function/const* 'data/succ []))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- succ [n] (function/app successor n))

(defn- add [l r] (function/app (function/const* 'algebra/nat-add []) l r))
(defn- seq-term [d0 n]
  (function/app (function/const* 'geometric/seq []) d0 n))
(defn- half-le-self [d]
  (function/app (function/const* 'nnrat/half-le-self []) d))
(defn- seq-step-monotone [d0 n]
  (function/app (function/const* 'geometric/seq-step-monotone []) d0 n))
(defn- at-most-reflexive [v]
  (function/app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))
(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- nat-equality [l r] (function/equality type-level nat l r))
(defn- nat-add-zero-right [x]
  (function/app (function/const* 'algebra/nat-add-zero-right []) x))
(defn- eq-transitive [x y z h1 h2]
  (function/app (function/const* 'equality/transitive [type-level])
                nat x y z h1 h2))

;; Definitions --------------------------------------------------------------

;; seq d0 n = (1/2)^n * d0, by recursion on n.
(def seq-spec
  {:name 'geometric/seq :kind :definition :universes []
   :type (function/arrow nnrat nat nnrat)
   :value
   (function/lam
    [['d0 nnrat] ['n nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     'd0
     (function/lam [['predecessor nat] ['previous nnrat]]
                   (nnrat-multiply half 'previous))
     'n))})

(def definition-specs [seq-spec])

;; Theorems -----------------------------------------------------------------

;; The recurrence: seq d0 (succ n) = (1/2) * seq d0 n  (Nat.rec computation rule).
(def step-unfold-spec
  {:name 'geometric/seq-step-unfold :universes []
   :type (function/forall
          [['d0 nnrat] ['n nat]]
          (equality nnrat
                    (seq-term 'd0 (succ 'n))
                    (nnrat-multiply half (seq-term 'd0 'n))))
   :value (function/lam
           [['d0 nnrat] ['n nat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (seq-term 'd0 (succ 'n))))})

;; General step monotonicity: seq d0 (succ n) <= seq d0 n for every n, because
;; seq d0 (succ n) = (1/2) * seq d0 n <= seq d0 n by nnrat/half-le-self.
(def step-monotone-spec
  {:name 'geometric/seq-step-monotone :universes []
   :type (function/forall
          [['d0 nnrat] ['n nat]]
          (nnrat-at-most (seq-term 'd0 (succ 'n)) (seq-term 'd0 'n)))
   :value (function/lam
           [['d0 nnrat] ['n nat]]
           (half-le-self (seq-term 'd0 'n)))})

;; Convergence bridge: running MORE contraction steps never increases the
;; distance -- seq d0 (n + k) <= seq d0 k for every n and k. By induction on n:
;; base (n = 0) is at-most-reflexive since add 0 k reduces to k; the step chains
;; one halving (seq-step-monotone) with the induction hypothesis via at-most
;; transitivity. This is what turns "iterate at least modulus(eps) times" into
;; "the distance is at most seq d0 (modulus eps)", completing the link to
;; convergence/converges-to once a modulus below eps is supplied.
(def seq-decreases-with-iteration-spec
  {:name 'geometric/seq-decreases-with-iteration :universes []
   :type (function/forall
          [['d0 nnrat] ['n nat] ['k nat]]
          (nnrat-at-most (seq-term 'd0 (add 'n 'k)) (seq-term 'd0 'k)))
   :value
   (function/lam
    [['d0 nnrat] ['n nat] ['k nat]]
    (let [motive (function/lam
                  [['m nat]]
                  (function/forall
                   [['j nat]]
                   (nnrat-at-most (seq-term 'd0 (add 'm 'j)) (seq-term 'd0 'j))))
          base (function/lam
                [['j nat]]
                (at-most-reflexive (seq-term 'd0 'j)))
          step (function/lam
                [['m nat] ['ih (function/app motive 'm)]]
                (function/lam
                 [['j nat]]
                 (at-most-transitive
                  (seq-term 'd0 (succ (add 'm 'j)))
                  (seq-term 'd0 (add 'm 'j))
                  (seq-term 'd0 'j)
                  (seq-step-monotone 'd0 (add 'm 'j))
                  (function/app 'ih 'j))))]
      (function/app
       (function/app
        (function/const* 'data/Nat.rec [zero-level])
        motive base step 'n)
       'k)))})

;; Sequence numerator is invariant under halving: num (seq d0 N) = num d0 for
;; every N. Each halving multiplies the numerator by num(1/2) = 1, and
;; num (seq d0 (succ N)) reduces to (num (seq d0 N)) + 0, so the numerator is
;; carried unchanged once the trailing + 0 is cancelled by nat-add-zero-right.
;; This is the numerator half of the sequence closed form seq d0 N =
;; (num d0) / (den d0 * 2^N) needed for the convergence modulus.
(def seq-numerator-invariant-spec
  {:name 'geometric/seq-numerator-invariant :universes []
   :type (function/forall
          [['d0 nnrat] ['n nat]]
          (nat-equality (numerator (seq-term 'd0 'n)) (numerator 'd0)))
   :value
   (function/lam
    [['d0 nnrat] ['n nat]]
    (let [motive (function/lam
                  [['m nat]]
                  (nat-equality (numerator (seq-term 'd0 'm)) (numerator 'd0)))
          base (function/app
                (function/const* 'equality/reflexive [type-level])
                nat (numerator 'd0))
          step (function/lam
                [['m nat] ['ih (function/app motive 'm)]]
                (eq-transitive
                 (numerator (seq-term 'd0 (succ 'm)))
                 (numerator (seq-term 'd0 'm))
                 (numerator 'd0)
                 (nat-add-zero-right (numerator (seq-term 'd0 'm)))
                 'ih))]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive base step 'n)))})

(def theorem-specs
  [step-unfold-spec step-monotone-spec seq-decreases-with-iteration-spec
   seq-numerator-invariant-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :geometric-sequence
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
