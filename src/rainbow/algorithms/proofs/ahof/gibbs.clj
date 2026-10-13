(ns rainbow.algorithms.proofs.ahof.gibbs
  "AHoF D8 Gibbs Sampling: an MCMC method that samples a joint distribution by
  repeatedly resampling one coordinate at a time from its full conditional given
  all the others. Unlike Metropolis-Hastings, a Gibbs step is always accepted --
  the chain always moves -- because the proposal IS the exact conditional. Each
  full-conditional draw is inverse-transform sampling over the conditional CDF:

      draws? cumulative u = decide (u <= cumulative)

  over the exact-rational conditional cumulative probability. Proved native and
  axiom-free: the conditional-draw test, and a worked draw u = 5 -- the value with
  cumulative 7 is drawn; the certificate 5 <= 7 as a native nnrat/at-most; and
  the value with cumulative 2 is skipped. That the coordinate is sampled from its
  full conditional is the inverse-transform property and is not proved here. The
  conditional CDF is the proved prefix-sum scan; the sweep order and RNG are
  executable. What is proved here is the draw decision at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gibbs`
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
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- draws? [cumulative u]
  (function/app (function/const* 'gibbs/draws? []) cumulative u))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; draws? cumulative u = decide (u <= cumulative)
(def draws-spec
  {:name 'gibbs/draws? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cumulative nnrat] ['u nnrat]]
                        (decide-at-most 'u 'cumulative))})

(def definition-specs [draws-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A uniform draw of 5 draws the value whose conditional cumulative reaches 7.
(def draws-value-spec
  {:name 'gibbs/draws-value :universes []
   :type (equality bool (draws? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (draws? (whole 7) (whole 5)))})

;; Certificate for the worked draw: 5 <= 7.
(def draw-is-from-conditional-spec
  {:name 'gibbs/draw-is-from-conditional :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A value whose conditional cumulative (2) is still below the draw (5) is
;; skipped.
(def skips-below-draw-spec
  {:name 'gibbs/skips-below-draw :universes []
   :type (equality bool (draws? (whole 2) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (draws? (whole 2) (whole 5)))})

(def theorem-specs
  [draws-value-spec draw-is-from-conditional-spec skips-below-draw-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-gibbs (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.gibbs))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
