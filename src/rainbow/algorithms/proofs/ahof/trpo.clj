(ns rainbow.algorithms.proofs.ahof.trpo
  "AHoF D51 Trust-Region Policy Optimization: improve a policy by maximizing a
  surrogate advantage objective subject to a trust-region constraint that the new
  policy stays close to the old one in KL divergence. (TRPO's monotone-improvement
  bound needs a max-KL penalty term; a mean-KL constraint alone does not imply it,
  and it is NOT proved here.) A candidate policy update is admissible exactly when its KL
  divergence from the current policy is within the trust radius delta:

      within-trust-region? kl delta = decide (kl <= delta)

  over the exact-rational KL divergence. Proved native and axiom-free: the
  trust-region admissibility test, the certificate that the admitted worked
  update stays within the trust region (1/10 <= 1/4 as a native nnrat/at-most),
  and that an update whose KL exceeds the radius is rejected (the line search
  must backtrack). The surrogate advantage,
  the natural-gradient step, and the KL estimation are executable; what is proved
  is the trust-region admissibility decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.trpo`
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

(defn- within-trust-region? [kl delta]
  (function/app (function/const* 'trpo/within-trust-region? []) kl delta))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; within-trust-region? kl delta = decide (kl <= delta)
(def within-trust-region-spec
  {:name 'trpo/within-trust-region? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['kl nnrat] ['delta nnrat]]
                        (decide-at-most 'kl 'delta))})

(def definition-specs [within-trust-region-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

;; A KL of 1/10 within trust radius delta = 1/4 is admissible.
(def update-admissible-spec
  {:name 'trpo/update-admissible :universes []
   :type (equality bool (within-trust-region? (fraction 1 9) (fraction 1 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-trust-region? (fraction 1 9) (fraction 1 3)))})

;; Certificate, worked instance: the admitted update stays within the trust region
;; (1/10 <= 1/4); no improvement bound is claimed.
(def admitted-stays-in-region-spec
  {:name 'trpo/admitted-stays-in-region :universes []
   :type (nnrat-at-most (fraction 1 9) (fraction 1 3))
   :value (at-most-proof (fraction 1 9) (fraction 1 3))})

;; An update whose KL (1/2) exceeds the radius (1/4) is rejected -- backtrack.
(def oversized-update-rejected-spec
  {:name 'trpo/oversized-update-rejected :universes []
   :type (equality bool (within-trust-region? (fraction 1 1) (fraction 1 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-trust-region? (fraction 1 1) (fraction 1 3)))})

(def theorem-specs
  [update-admissible-spec admitted-stays-in-region-spec
   oversized-update-rejected-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-trpo (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.trpo))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
