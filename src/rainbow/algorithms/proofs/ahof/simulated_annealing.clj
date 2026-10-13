(ns rainbow.algorithms.proofs.ahof.simulated-annealing
  "AHoF Simulated Annealing: a global optimization metaheuristic that escapes local
  optima by sometimes accepting WORSE solutions -- with a probability that shrinks
  as a 'temperature' cools -- inspired by the annealing of metals. A downhill move
  (better objective) is always accepted; an uphill move to a worse candidate is
  accepted only when a random draw u falls under the Metropolis acceptance
  probability exp(-delta/T):

      accepts-uphill? u accept-probability = decide (u <= accept-probability)

  over exact-rational values. Proved native and axiom-free: the uphill-acceptance
  test, and worked instances -- a draw of 1/4 under probability 1/2 accepts the
  worse move; the certificate 1/4 <= 1/2 as a native nnrat/at-most; and a draw of
  3/4 rejects the uphill move. No claim about the acceptance rate is proved. The
  cooling schedule, neighbor proposal, and exp/RNG are executable; what is proved
  is the acceptance decision at these instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.simulated-annealing`
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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- accepts-uphill? [u accept-probability]
  (function/app (function/const* 'simulated-annealing/accepts-uphill? [])
                u accept-probability))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; accepts-uphill? u accept-probability = decide (u <= accept-probability)
(def accepts-uphill-spec
  {:name 'simulated-annealing/accepts-uphill? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['u nnrat] ['accept-probability nnrat]]
                        (decide-at-most 'u 'accept-probability))})

(def definition-specs [accepts-uphill-spec])

;; Theorems -----------------------------------------------------------------

;; A draw of 1/4 under the acceptance probability 1/2 accepts the worse move.
(def accepts-worse-move-spec
  {:name 'simulated-annealing/accepts-worse-move :universes []
   :type (equality bool (accepts-uphill? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-uphill? (fraction 1 3) (fraction 1 1)))})

;; Certificate, worked instance: the accepted draw lies under the acceptance
;; probability (1/4 <= 1/2).
(def acceptance-within-probability-spec
  {:name 'simulated-annealing/acceptance-within-probability :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

;; A draw of 3/4 above the acceptance probability 1/2 rejects the uphill move.
(def rejects-worse-move-spec
  {:name 'simulated-annealing/rejects-worse-move :universes []
   :type (equality bool (accepts-uphill? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-uphill? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [accepts-worse-move-spec acceptance-within-probability-spec
   rejects-worse-move-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-simulated-annealing
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
