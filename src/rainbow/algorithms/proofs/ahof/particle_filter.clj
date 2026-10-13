(ns rainbow.algorithms.proofs.ahof.particle-filter
  "AHoF D10 Particle Filter (sequential Monte Carlo): approximate a filtering
  distribution by a weighted set of particles, propagated and reweighted each
  step, then RESAMPLED to combat weight degeneracy. Resampling draws new
  particles in proportion to their normalized weights via inverse-transform
  sampling over the cumulative weight distribution:

      resamples? cumulative u = decide (u <= cumulative)

  over the exact-rational cumulative weight. Proved native and axiom-free, as
  worked instances: a draw of 4 against cumulative weight 6 resamples; the worked
  certificate 4 <= 6 (native nnrat/at-most); and a draw of 4 against cumulative
  weight 2 skips. That resampling is proportional to weight and keeps the
  approximation unbiased is the algorithm's classical property, not proved here;
  the cumulative weights, the propagation/likelihood models and RNG are
  executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.particle-filter`
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

(defn- resamples? [cumulative u]
  (function/app (function/const* 'particle-filter/resamples? []) cumulative u))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; resamples? cumulative u = decide (u <= cumulative)
(def resamples-spec
  {:name 'particle-filter/resamples? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cumulative nnrat] ['u nnrat]]
                        (decide-at-most 'u 'cumulative))})

(def definition-specs [resamples-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A draw of 4 resamples the particle whose cumulative weight reaches 6.
(def resamples-particle-spec
  {:name 'particle-filter/resamples-particle :universes []
   :type (equality bool (resamples? (whole 6) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (resamples? (whole 6) (whole 4)))})

;; Worked certificate for the resample above: 4 <= 6 (proportional, unbiased
;; resampling is classical, not proved here).
(def resample-is-proportional-spec
  {:name 'particle-filter/resample-is-proportional :universes []
   :type (nnrat-at-most (whole 4) (whole 6))
   :value (at-most-proof (whole 4) (whole 6))})

;; A particle whose cumulative weight (2) is still below the draw (4) is skipped.
(def skips-below-draw-spec
  {:name 'particle-filter/skips-below-draw :universes []
   :type (equality bool (resamples? (whole 2) (whole 4))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (resamples? (whole 2) (whole 4)))})

(def theorem-specs
  [resamples-particle-spec resample-is-proportional-spec skips-below-draw-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-particle-filter (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.particle-filter))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
