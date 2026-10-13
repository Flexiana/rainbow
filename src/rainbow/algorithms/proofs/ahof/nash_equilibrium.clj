(ns rainbow.algorithms.proofs.ahof.nash-equilibrium
  "AHoF D77 Nash Equilibrium (support enumeration): a strategy profile is a Nash
  equilibrium when no player can gain by unilaterally deviating. The per-player
  stability test compares the payoff of a candidate deviation against the current
  payoff:

      no-profitable-deviation? current deviation = decide (deviation <= current).

  When every player's every deviation is no better than the current payoff, the
  profile is an equilibrium. Proved native and axiom-free: the no-deviation decision,
  a stable profile, the native at-most stability certificate, and a profitable
  deviation that breaks stability. Requires audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.nash-equilibrium`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

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
(defn- no-profitable-deviation? [current deviation]
  (function/app (function/const* 'nash/no-profitable-deviation? []) current deviation))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def no-deviation-spec
  {:name 'nash/no-profitable-deviation? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['current nnrat] ['deviation nnrat]]
                        (decide-at-most 'deviation 'current))})

(def definition-specs [no-deviation-spec])

;; A current payoff 3/4 beats a deviation worth 1/2: the player will not deviate.
(def stable-profile-spec
  {:name 'nash/stable-profile :universes []
   :type (equality bool (no-profitable-deviation? (fraction 3 3) (fraction 1 1))
                   true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (no-profitable-deviation? (fraction 3 3) (fraction 1 1)))})

;; Certificate: the deviation payoff really is at most the current (1/2 <= 3/4).
(def stability-certificate-spec
  {:name 'nash/stability-certificate :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

;; A deviation worth 3/4 exceeds the current 1/2: the player deviates, breaking
;; equilibrium.
(def profitable-deviation-spec
  {:name 'nash/profitable-deviation :universes []
   :type (equality bool (no-profitable-deviation? (fraction 1 1) (fraction 3 3))
                   false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (no-profitable-deviation? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [stable-profile-spec stability-certificate-spec profitable-deviation-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-nash-equilibrium (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.nash-equilibrium))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
