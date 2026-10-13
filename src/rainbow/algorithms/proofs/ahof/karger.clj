(ns rainbow.algorithms.proofs.ahof.karger
  "AHoF Karger's Min-Cut Algorithm (randomized): estimate the minimum cut of an
  undirected graph -- the fewest edges whose removal disconnects it -- by repeatedly
  CONTRACTING a uniformly random edge (merging its endpoints, keeping parallel
  edges) until two supernodes remain; the edges between them form a cut. A single
  trial finds the true minimum with probability >= 2/(n(n-1)), so running many
  trials and keeping the smallest result succeeds with high probability. Across
  trials the best cut is updated by:

      keep-smaller-cut? candidate current-best = decide (candidate <= current-best)

  over exact-rational (integer) cut sizes. Proved native and axiom-free: the
  keep-smaller test; that a smaller candidate cut replaces the current best; the
  certificate that a kept candidate is at most the previous best (native
  nnrat/at-most) -- the running minimum only decreases; and that a larger candidate
  is discarded. The random contraction and trial loop are executable; what is proved
  is the best-cut update decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.karger`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- keep-smaller-cut? [candidate current-best]
  (function/app (function/const* 'karger/keep-smaller-cut? []) candidate current-best))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; keep-smaller-cut? candidate current-best = decide (candidate <= current-best)
(def keep-smaller-cut-spec
  {:name 'karger/keep-smaller-cut? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['candidate nnrat] ['current-best nnrat]]
                        (decide-at-most 'candidate 'current-best))})

(def definition-specs [keep-smaller-cut-spec])

;; Theorems -----------------------------------------------------------------

;; A trial yielding a cut of 2 improves on the current best of 5: keep it.
(def smaller-cut-kept-spec
  {:name 'karger/smaller-cut-kept :universes []
   :type (equality bool (keep-smaller-cut? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-smaller-cut? (whole 2) (whole 5)))})

;; Certificate: a kept candidate is at most the previous best (2 <= 5), so the
;; running minimum only decreases.
(def kept-cut-at-most-previous-spec
  {:name 'karger/kept-cut-at-most-previous :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A trial yielding a larger cut of 7 is discarded (best stays 5).
(def larger-cut-discarded-spec
  {:name 'karger/larger-cut-discarded :universes []
   :type (equality bool (keep-smaller-cut? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-smaller-cut? (whole 7) (whole 5)))})

(def theorem-specs
  [smaller-cut-kept-spec kept-cut-at-most-previous-spec larger-cut-discarded-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-karger (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.karger))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
