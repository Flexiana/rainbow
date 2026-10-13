(ns rainbow.algorithms.proofs.metropolis
  "AHoF V22 Metropolis-Hastings acceptance (also the acceptance rule of
  Simulated Annealing): a proposed state is scored by an energy (cost), and the
  Metropolis rule always accepts a downhill proposal, while an uphill proposal is
  accepted only with probability exp(-(E' - E)/T). The deterministic core is the
  downhill test,

      accepts-downhill? proposed current = decide (proposed <= current)

  over the decidable rational order. Proved on worked instances: a proposal of
  energy 3 against current 5 is accepted (the decision computes to true); the
  certificate 3 <= 5 as a native nnrat/at-most; and a proposal of 8 against 5 is
  not deterministically accepted. The stochastic uphill acceptance (the Boltzmann
  factor) and the proposal kernel are executable concerns; what is proved here is
  the acceptance test on these instances, not a property of the chain.

  Requires nnrat/at-most, audit/decide-nnrat-at-most, and
  nnrat/decide-at-most-true-sound (carried by the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.metropolis`
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

(defn- accepts-downhill? [proposed current]
  (function/app (function/const* 'metropolis/accepts-downhill? [])
                proposed current))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; accepts-downhill? proposed current = decide (proposed <= current)
(def accepts-downhill-spec
  {:name 'metropolis/accepts-downhill? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['proposed nnrat] ['current nnrat]]
                        (decide-at-most 'proposed 'current))})

(def definition-specs [accepts-downhill-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A downhill proposal (energy 3) against the current state (energy 5) is
;; accepted (3 <= 5 decides true).
(def accepts-downhill-move-spec
  {:name 'metropolis/accepts-downhill-move :universes []
   :type (equality bool (accepts-downhill? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-downhill? (whole 3) (whole 5)))})

;; Worked instance: the accepted downhill move does not increase the energy
;; (proposed 3 <= current 5).
(def downhill-does-not-worsen-spec
  {:name 'metropolis/downhill-does-not-worsen :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; An uphill proposal (energy 8) against the current (5) is not deterministically
;; accepted (8 <= 5 decides false); it defers to the Boltzmann factor.
(def uphill-not-deterministic-spec
  {:name 'metropolis/uphill-not-deterministic :universes []
   :type (equality bool (accepts-downhill? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (accepts-downhill? (whole 8) (whole 5)))})

(def theorem-specs
  [accepts-downhill-move-spec downhill-does-not-worsen-spec
   uphill-not-deterministic-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :metropolis (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.metropolis))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
