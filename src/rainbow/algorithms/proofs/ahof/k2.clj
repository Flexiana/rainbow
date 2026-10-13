(ns rainbow.algorithms.proofs.ahof.k2
  "AHoF D15 K2 Graph Search: greedy Bayesian-network structure learning. Following
  a fixed variable ordering, K2 adds to a node the candidate parent whose
  addition most improves the local (decomposable) score, and stops when no
  addition improves it. The greedy-acceptance test is the decidable score
  comparison:

      improves? new-score old-score = decide (old-score <= new-score)

  over the exact-rational local scores (BDeu / BIC). Proved native and axiom-free,
  as worked instances: a parent raising the score from 5 to 8 is accepted; the
  worked certificate 5 <= 8 (native nnrat/at-most); and a parent lowering the
  score from 5 to 4 is rejected. That K2's greedy hill-climb is monotone for all
  scores is the algorithm's classical property, not proved here. The score
  function, the ordering, and the parent enumeration are executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.k2`
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

(defn- improves? [new-score old-score]
  (function/app (function/const* 'k2/improves? []) new-score old-score))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; improves? new old = decide (old <= new)
(def improves-spec
  {:name 'k2/improves? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['new-score nnrat] ['old-score nnrat]]
                        (decide-at-most 'old-score 'new-score))})

(def definition-specs [improves-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Adding a parent that raises the score (8 from 5) is accepted.
(def accepts-improvement-spec
  {:name 'k2/accepts-improvement :universes []
   :type (equality bool (improves? (whole 8) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (improves? (whole 8) (whole 5)))})

;; Worked certificate for the accepted parent above: 5 <= 8.
(def accepted-does-not-decrease-spec
  {:name 'k2/accepted-does-not-decrease :universes []
   :type (nnrat-at-most (whole 5) (whole 8))
   :value (at-most-proof (whole 5) (whole 8))})

;; A parent that lowers the score (4 from 5) is rejected -- search halts.
(def rejects-non-improvement-spec
  {:name 'k2/rejects-non-improvement :universes []
   :type (equality bool (improves? (whole 4) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (improves? (whole 4) (whole 5)))})

(def theorem-specs
  [accepts-improvement-spec accepted-does-not-decrease-spec
   rejects-non-improvement-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-k2
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
