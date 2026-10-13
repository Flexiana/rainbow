(ns rainbow.algorithms.proofs.ahof.viterbi
  "AHoF Viterbi Algorithm: find the single most-likely hidden-state sequence of a
  Hidden Markov Model given observations -- the standard decoder for HMMs (speech
  recognition, POS tagging, gene finding). The DP value delta_t(j) is the highest
  probability of any state path ending in state j at time t:

      path-prob prev transition emission = prev * transition * emission
      cell current-best candidate        = max(current-best, candidate)

  where the candidate for predecessor i is delta_{t-1}(i) * a_ij * b_j(o_t), and
  the cell takes the max over predecessors, over exact-rational probabilities.
  Proved native and axiom-free: the path-probability product; a worked path
  probability; the max-selection cell (decidable rational max via logic/if-data); a
  worked cell; and the certificate that the surviving path probability dominates a
  competing one (native nnrat/at-most). The backpointer bookkeeping and
  observation sequence are executable; what is proved is the Viterbi cell recurrence.

  Requires nnrat/multiply, audit/decide-nnrat-at-most, logic/if-data,
  nnrat/at-most, nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.viterbi`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nnrat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- path-prob [prev transition emission]
  (function/app (function/const* 'viterbi/path-prob []) prev transition emission))
(defn- cell [current-best candidate]
  (function/app (function/const* 'viterbi/cell []) current-best candidate))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; path-prob prev transition emission = prev * transition * emission
(def path-prob-spec
  {:name 'viterbi/path-prob :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['prev nnrat] ['transition nnrat] ['emission nnrat]]
                        (nnrat-multiply (nnrat-multiply 'prev 'transition)
                                        'emission))})

;; cell current-best candidate = max(current-best, candidate)
(def cell-spec
  {:name 'viterbi/cell :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['current-best nnrat] ['candidate nnrat]]
                        (if-nnrat (decide-at-most 'current-best 'candidate)
                                  'candidate 'current-best))})

(def definition-specs [path-prob-spec cell-spec])

;; Theorems -----------------------------------------------------------------

;; Path probability: prev 1/2, transition 1/2, emission 1 -> 1/4.
(def path-prob-example-spec
  {:name 'viterbi/path-prob-example :universes []
   :type (equality nnrat
                   (path-prob (fraction 1 1) (fraction 1 1) (whole 1))
                   (fraction 1 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (path-prob (fraction 1 1) (fraction 1 1) (whole 1)))})

;; The cell keeps the more-probable path (1/2 over 1/4).
(def keeps-most-probable-spec
  {:name 'viterbi/keeps-most-probable :universes []
   :type (equality nnrat (cell (fraction 1 3) (fraction 1 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (cell (fraction 1 3) (fraction 1 1)))})

;; Certificate: the surviving path probability dominates the competitor
;; (1/4 <= 1/2).
(def survivor-dominates-spec
  {:name 'viterbi/survivor-dominates :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def theorem-specs
  [path-prob-example-spec keeps-most-probable-spec survivor-dominates-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-viterbi
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
