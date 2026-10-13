(ns rainbow.math.rational.nnrat.multiply-monotone
  "Universal monotonicity of nonnegative-rational multiplication under the rational
  order -- the algebra gap flagged in rainbow-universal-foundation-layer that blocks
  convex-combination / weighted-average bounds:

      multiply-monotone-base : base-at-most a b -> base-at-most (c*a) (c*b)   (all c a b)
      multiply-monotone      : a <= b           -> (c*a) <= (c*b)            (all c a b)

  The base lemma is pure nat reasoning: with num/den written out,
      base-at-most a b       = (num a * den b) <= (num b * den a)
      base-at-most (c*a)(c*b)= ((num c * num a) * (den c * den b))
                            <= ((num c * num b) * (den c * den a))
  Reassociate both sides by nat/multiply-four-reorder into
      (num c * den c) * (num a * den b)  <=  (num c * den c) * (num b * den a)
  which is nat/multiply-left-monotone applied to the hypothesis; the product
  denominators (den c * den b) are converted to the packed product-denominator
  succ(combine ..) via the nnrat/denominator-combine law, transported with
  nat/at-most-rewrite-left / -right.  The full theorem lifts the base lemma across the
  reflexive-transitive closure nnrat/at-most by instantiating the closure recursor at
  the motive (\\y. c*a <= c*y): reflexivity for the base, and for each step
  at-most-from-cross (multiply-monotone-base ..) chained by at-most-transitive.

  Native and axiom-free; chains rainbow.algorithms.proofs.decision-guarantee-audit (order),
  rainbow.math.nat.semiring / nat-order (nat algebra), and nonnegative-rational."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def successor (function/const* 'data/succ []))

;; nat-level building blocks (must be the SAME consts nnrat/base-at-most reduces to)
(defn- nsucc [v] (function/app successor v))
(defn- nmul [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- symmetric [l r same]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r same))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))

;; nnrat accessors / operations
(defn- rnum [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- rmul [c x] (function/app (function/const* 'nnrat/multiply []) c x))
(defn- base-le [a b] (function/app (function/const* 'nnrat/base-at-most []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))

;; base monotonicity: base-at-most a b -> base-at-most (c*a) (c*b)
(def multiply-monotone-base-spec
  {:name 'nnrat/multiply-monotone-base :universes []
   :type (function/forall
          [['c nnrat] ['a nnrat] ['b nnrat]
           ['h (base-le 'a 'b)]]
          (base-le (rmul 'c 'a) (rmul 'c 'b)))
   :value
   (function/lam
    [['c nnrat] ['a nnrat] ['b nnrat] ['h (base-le 'a 'b)]]
    (let [nc (rnum 'c) na (rnum 'a) nb (rnum 'b)
          dpc (dpre 'c) dpa (dpre 'a) dpb (dpre 'b)
          da (nsucc dpa) db (nsucc dpb) dc (nsucc dpc)
          NA (nmul nc na) NB (nmul nc nb)
          P (nmul nc dc)
          combA (nsucc (combine dpc dpa))
          combB (nsucc (combine dpc dpb))
          ;; law : succ(combine L R) = (succ L)*(succ R)
          lawA (function/app (function/const* 'nnrat/denominator-combine []) dpc dpa)
          lawB (function/app (function/const* 'nnrat/denominator-combine []) dpc dpb)
          ;; mono : P*(na*db) <= P*(nb*da)
          mono (function/app (function/const* 'nat/multiply-left-monotone [])
                             P (nmul na db) (nmul nb da) 'h)
          ;; four-reorder: NA*(dc*db) = P*(na*db) ; NB*(dc*da) = P*(nb*da)
          fr-a (function/app (function/const* 'nat/multiply-four-reorder [])
                             nc na dc db)
          fr-b (function/app (function/const* 'nat/multiply-four-reorder [])
                             nc nb dc da)
          ;; r1: rewrite left P*(na*db) -> NA*(dc*db)
          r1 (function/app (function/const* 'nat/at-most-rewrite-left [])
                           (nmul NA (nmul dc db)) (nmul P (nmul na db))
                           (nmul P (nmul nb da)) fr-a mono)
          ;; r2: rewrite left NA*(dc*db) -> NA*combB
          congB (congruent (function/lam [['v nat]] (nmul NA 'v))
                           combB (nmul dc db) lawB)
          r2 (function/app (function/const* 'nat/at-most-rewrite-left [])
                           (nmul NA combB) (nmul NA (nmul dc db))
                           (nmul P (nmul nb da)) congB r1)
          ;; r3: rewrite right P*(nb*da) -> NB*(dc*da)
          sym-fr-b (symmetric (nmul NB (nmul dc da)) (nmul P (nmul nb da)) fr-b)
          r3 (function/app (function/const* 'nat/at-most-rewrite-right [])
                           (nmul NA combB) (nmul P (nmul nb da))
                           (nmul NB (nmul dc da)) sym-fr-b r2)
          ;; r4: rewrite right NB*(dc*da) -> NB*combA
          sym-law-a (symmetric combA (nmul dc da) lawA)
          congA (congruent (function/lam [['v nat]] (nmul NB 'v))
                           (nmul dc da) combA sym-law-a)
          r4 (function/app (function/const* 'nat/at-most-rewrite-right [])
                           (nmul NA combB) (nmul NB (nmul dc da))
                           (nmul NB combA) congA r3)]
      r4))})

;; full monotonicity across the closure: a <= b -> (c*a) <= (c*b)
(def multiply-monotone-spec
  {:name 'nnrat/multiply-monotone :universes []
   :type (function/forall
          [['c nnrat] ['a nnrat] ['b nnrat]
           ['h (rat-le 'a 'b)]]
          (rat-le (rmul 'c 'a) (rmul 'c 'b)))
   :value
   (function/lam
    [['c nnrat] ['a nnrat] ['b nnrat] ['h (rat-le 'a 'b)]]
    (let [motive (function/lam [['y nnrat]]
                               (rat-le (rmul 'c 'a) (rmul 'c 'y)))
          step (function/lam
                [['before nnrat] ['after nnrat]
                 ['o (base-le 'before 'after)]
                 ['acc (rat-le (rmul 'c 'a) (rmul 'c 'before))]]
                (let [lifted (function/app
                              (function/const* 'nnrat/at-most-from-cross [])
                              (rmul 'c 'before) (rmul 'c 'after)
                              (function/app
                               (function/const* 'nnrat/multiply-monotone-base [])
                               'c 'before 'after 'o))]
                  (function/app (function/const* 'nnrat/at-most-transitive [])
                                (rmul 'c 'a) (rmul 'c 'before) (rmul 'c 'after)
                                'acc lifted)))
          base-case (function/app (function/const* 'nnrat/at-most-reflexive [])
                                  (rmul 'c 'a))]
      (function/app 'h motive step base-case)))})

(def definition-specs [])
(def theorem-specs [multiply-monotone-base-spec multiply-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nnrat-multiply-monotone (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.multiply-monotone))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
