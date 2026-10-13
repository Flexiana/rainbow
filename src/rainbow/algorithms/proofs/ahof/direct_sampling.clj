(ns rainbow.algorithms.proofs.ahof.direct-sampling
  "AHoF D5 Direct Sampling: draw a sample from a Bayesian network by ancestral
  sampling, drawing each variable from its conditional distribution given already
  sampled parents. A single categorical draw uses inverse-transform sampling:
  given a uniform draw u in [0,1) and the running cumulative probability, the
  category is selected once the cumulative reaches u:

      selects? cumulative u = decide (u <= cumulative)

  over the exact-rational cumulative probability. Defined: the selection test.
  Proved native and axiom-free, as worked instances: cumulative 7 with draw 5
  selects, cumulative 3 with draw 5 skips, and the worked certificate 5 <= 7
  (native nnrat/at-most). That inverse-transform sampling is a valid draw from the
  distribution is classical and not proved here. The topological order, the CDF
  construction, and the RNG are executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.direct-sampling`
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

(defn- selects? [cumulative u]
  (function/app (function/const* 'direct-sampling/selects? []) cumulative u))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; selects? cumulative u = decide (u <= cumulative)
(def selects-spec
  {:name 'direct-sampling/selects? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cumulative nnrat] ['u nnrat]]
                        (decide-at-most 'u 'cumulative))})

(def definition-specs [selects-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; When the cumulative mass (7) reaches the draw (5), the category is selected.
(def selects-category-spec
  {:name 'direct-sampling/selects-category :universes []
   :type (equality bool (selects? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (selects? (whole 7) (whole 5)))})

;; Worked certificate 5 <= 7 (validity of the sampler is not proved here).
(def selection-is-valid-spec
  {:name 'direct-sampling/selection-is-valid :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A category whose cumulative (3) is still below the draw (5) is skipped.
(def skips-below-draw-spec
  {:name 'direct-sampling/skips-below-draw :universes []
   :type (equality bool (selects? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (selects? (whole 3) (whole 5)))})

(def theorem-specs
  [selects-category-spec selection-is-valid-spec skips-below-draw-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-direct-sampling (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.direct-sampling))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
