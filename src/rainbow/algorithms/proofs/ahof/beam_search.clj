(ns rainbow.algorithms.proofs.ahof.beam-search
  "AHoF D-family Beam Search: a bounded-breadth heuristic search that, at each
  level, expands only the K highest-scoring partial solutions (the beam) instead
  of the full frontier -- trading completeness for tractable memory, as in machine
  translation decoding and structured prediction. A candidate stays in the beam
  exactly when its score meets the beam's cutoff (the K-th best score at that
  level):

      in-beam? score cutoff = decide (cutoff <= score)

  over exact-rational candidate scores. Proved native and axiom-free: the
  beam-membership test; that a high-scoring candidate is kept; that a low-scoring
  candidate is pruned; and the certificate that a retained candidate really meets
  the cutoff (cutoff <= score as native nnrat/at-most). The successor expansion and
  the cutoff (K-th order statistic) are executable; what is proved is the beam
  pruning decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.beam-search`
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

(defn- in-beam? [score cutoff]
  (function/app (function/const* 'beam-search/in-beam? []) score cutoff))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; in-beam? score cutoff = decide (cutoff <= score)
(def in-beam-spec
  {:name 'beam-search/in-beam? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['score nnrat] ['cutoff nnrat]]
                        (decide-at-most 'cutoff 'score))})

(def definition-specs [in-beam-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A candidate scoring 7 with beam cutoff 5 stays in the beam.
(def keeps-high-scorer-spec
  {:name 'beam-search/keeps-high-scorer :universes []
   :type (equality bool (in-beam? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-beam? (whole 7) (whole 5)))})

;; Certificate: a retained candidate's score is at least the cutoff (5 <= 7).
(def retained-meets-cutoff-spec
  {:name 'beam-search/retained-meets-cutoff :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A candidate scoring 3 below the cutoff 5 is pruned from the beam.
(def prunes-low-scorer-spec
  {:name 'beam-search/prunes-low-scorer :universes []
   :type (equality bool (in-beam? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-beam? (whole 3) (whole 5)))})

(def theorem-specs
  [keeps-high-scorer-spec retained-meets-cutoff-spec prunes-low-scorer-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-beam-search (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.beam-search))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
