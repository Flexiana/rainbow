(ns rainbow.algorithms.proofs.ahof.falsification
  "AHoF V9 Direct Sampling Falsification: the simplest falsification method --
  sample inputs, simulate, and return the first whose specification robustness
  has dropped to the falsification margin. An input falsifies the specification
  when its robustness margin is at most the threshold:

      falsifies? robustness margin = decide (robustness <= margin)

  over the decidable rational order (robustness measured as a nonnegative margin
  above violation; margin 0 is exact violation). Defined: the falsification
  test. Proved native and axiom-free, as worked instances: robustness 1 with
  margin 2 is flagged, robustness 5 with margin 2 is not, and the worked
  certificate 1 <= 2 (native nnrat/at-most). Soundness of the test for all
  inputs (every reported counterexample is genuine) is not proved here. The input
  sampling and the simulation that produces the robustness value are executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most, and
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.falsification`
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

(defn- falsifies? [robustness margin]
  (function/app (function/const* 'falsification/falsifies? []) robustness margin))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; falsifies? robustness margin = decide (robustness <= margin)
(def falsifies-spec
  {:name 'falsification/falsifies? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['robustness nnrat] ['margin nnrat]]
                        (decide-at-most 'robustness 'margin))})

(def definition-specs [falsifies-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A low-robustness sample (1 <= margin 2) is flagged as a counterexample.
(def flags-counterexample-spec
  {:name 'falsification/flags-counterexample :universes []
   :type (equality bool (falsifies? (whole 1) (whole 2))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (falsifies? (whole 1) (whole 2)))})

;; Worked certificate 1 <= 2. Soundness for all inputs is not proved here.
(def counterexample-is-sound-spec
  {:name 'falsification/counterexample-is-sound :universes []
   :type (nnrat-at-most (whole 1) (whole 2))
   :value (at-most-proof (whole 1) (whole 2))})

;; A robust sample (5 > margin 2) is not flagged; sampling must continue.
(def robust-not-flagged-spec
  {:name 'falsification/robust-not-flagged :universes []
   :type (equality bool (falsifies? (whole 5) (whole 2))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (falsifies? (whole 5) (whole 2)))})

(def theorem-specs
  [flags-counterexample-spec counterexample-is-sound-spec
   robust-not-flagged-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-falsification (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.falsification))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
