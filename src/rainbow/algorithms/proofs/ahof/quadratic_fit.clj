(ns rainbow.algorithms.proofs.ahof.quadratic-fit
  "AHoF O10 Quadratic Fit Search: fit a parabola through three sampled points and
  step toward its vertex, keeping the three lowest-valued points as the bracket
  shrinks. The bracket-tracking core is the minimum of the three sampled values:

      best-of-two a b     = if (a <= b) then a else b
      best-of-three a b c = best-of-two (best-of-two a b) c

  over exact rationals (min via the nnrat eliminator). Proved native and axiom-free:
  the pairwise min, the three-way min, and worked instances retaining the smallest
  sampled value. Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.quadratic-fit`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- best-of-two [a b]
  (function/app (function/const* 'quadfit/best-of-two []) a b))
(defn- best-of-three [a b c]
  (function/app (function/const* 'quadfit/best-of-three []) a b c))

;; best-of-two a b = if (a <= b) then a else b
(def best-of-two-spec
  {:name 'quadfit/best-of-two :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'a 'b))
                                      (decide-at-most 'a 'b) 'a 'b))})

;; best-of-three a b c = best-of-two (best-of-two a b) c
(def best-of-three-spec
  {:name 'quadfit/best-of-three :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat] ['c nnrat]]
                        (best-of-two (best-of-two 'a 'b) 'c))})

(def definition-specs [best-of-two-spec best-of-three-spec])

;; The min of 3/4, 1/2, 1 is 1/2 (the middle sample is smallest).
(def keeps-smallest-spec
  {:name 'quadfit/keeps-smallest :universes []
   :type (equality nnrat (best-of-three (fraction 3 3) (fraction 1 1) (whole 1))
                   (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-of-three (fraction 3 3) (fraction 1 1) (whole 1)))})

;; ...and when the smallest is first, it is still retained.
(def keeps-smallest-first-spec
  {:name 'quadfit/keeps-smallest-first :universes []
   :type (equality nnrat (best-of-three (fraction 1 1) (fraction 3 3) (whole 1))
                   (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-of-three (fraction 1 1) (fraction 3 3) (whole 1)))})

;; The pairwise min of 3/4 and 1/2 is 1/2.
(def pairwise-min-spec
  {:name 'quadfit/pairwise-min :universes []
   :type (equality nnrat (best-of-two (fraction 3 3) (fraction 1 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (best-of-two (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [keeps-smallest-spec keeps-smallest-first-spec pairwise-min-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-quadratic-fit (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.quadratic-fit))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
