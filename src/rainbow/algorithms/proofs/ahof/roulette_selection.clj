(ns rainbow.algorithms.proofs.ahof.roulette-selection
  "AHoF genetic-algorithm operator: fitness-proportionate (roulette-wheel)
  selection. Individuals are chosen for reproduction with probability
  proportional to fitness. The wheel is the cumulative fitness (a prefix-sum
  scan); a spin s selects the first individual whose cumulative fitness reaches
  s:

      lands? cumulative s = decide (s <= cumulative)

  over exact-rational cumulative fitness. Proved native and axiom-free: the
  landing test and worked instances on concrete values -- spin 6 lands on an
  individual with cumulative fitness 9; the worked certificate 6 <= 9 as a native
  nnrat/at-most; and an individual with cumulative fitness 4 is passed over by
  spin 6. The cumulative wheel (a prefix-sum scan) and the RNG spin are
  executable. What is proved here is the landing decision at these instances;
  that selection probability is proportional to fitness is the classical property
  of the operator and is not proved here.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.roulette-selection`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- lands? [cumulative s]
  (function/app (function/const* 'roulette/lands? []) cumulative s))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; lands? cumulative s = decide (s <= cumulative)
(def lands-spec
  {:name 'roulette/lands? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['cumulative nnrat] ['s nnrat]]
                        (decide-at-most 's 'cumulative))})

(def definition-specs [lands-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A spin of 6 lands on the individual whose cumulative fitness reaches 9.
(def lands-on-individual-spec
  {:name 'roulette/lands-on-individual :universes []
   :type (equality bool (lands? (whole 9) (whole 6))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (lands? (whole 9) (whole 6)))})

;; Worked certificate: spin 6 <= cumulative fitness 9.
(def landing-is-valid-spec
  {:name 'roulette/landing-is-valid :universes []
   :type (nnrat-at-most (whole 6) (whole 9))
   :value (at-most-proof (whole 6) (whole 9))})

;; An individual whose cumulative fitness (4) is still below the spin (6) is
;; passed over.
(def passes-over-below-spin-spec
  {:name 'roulette/passes-over-below-spin :universes []
   :type (equality bool (lands? (whole 4) (whole 6))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (lands? (whole 4) (whole 6)))})

(def theorem-specs
  [lands-on-individual-spec landing-is-valid-spec passes-over-below-spin-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-roulette-selection
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
