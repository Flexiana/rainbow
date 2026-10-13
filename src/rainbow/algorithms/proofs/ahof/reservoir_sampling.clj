(ns rainbow.algorithms.proofs.ahof.reservoir-sampling
  "AHoF Reservoir Sampling (Algorithm R): draw a uniform random sample of fixed
  size k from a STREAM of unknown, possibly huge length in a SINGLE PASS and O(k)
  memory -- used for log sampling, streaming analytics, and dataset subsampling.
  The reservoir holds the first k items; for each later item i (1-indexed) a random
  slot j in [1, i] is drawn, and the item REPLACES reservoir slot j exactly when
  the slot falls within the reservoir:

      replaces? slot k = decide (slot <= k)

  which happens with probability k/i, keeping every seen item equally likely. Proved
  native and axiom-free: the replacement test; that a slot within the reservoir
  triggers a replacement; the certificate that a replacing slot really is within the
  reservoir (native nnrat/at-most) -- so uniformity is preserved; and that a slot
  beyond the reservoir discards the item. The RNG and the reservoir array are
  executable; what is proved is the replacement decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.reservoir-sampling`
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
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- replaces? [slot k]
  (function/app (function/const* 'reservoir-sampling/replaces? []) slot k))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; replaces? slot k = decide (slot <= k)
(def replaces-spec
  {:name 'reservoir-sampling/replaces? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['slot nnrat] ['k nnrat]]
                        (decide-at-most 'slot 'k))})

(def definition-specs [replaces-spec])

;; Theorems -----------------------------------------------------------------

;; A drawn slot 2 within a reservoir of size 3 replaces that slot.
(def slot-in-reservoir-replaces-spec
  {:name 'reservoir-sampling/slot-in-reservoir-replaces :universes []
   :type (equality bool (replaces? (whole 2) (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (replaces? (whole 2) (whole 3)))})

;; Uniformity certificate: a replacing slot is within the reservoir (2 <= 3).
(def replacement-within-reservoir-spec
  {:name 'reservoir-sampling/replacement-within-reservoir :universes []
   :type (nnrat-at-most (whole 2) (whole 3))
   :value (at-most-proof (whole 2) (whole 3))})

;; A drawn slot 5 beyond a reservoir of size 3 discards the item.
(def slot-beyond-reservoir-discards-spec
  {:name 'reservoir-sampling/slot-beyond-reservoir-discards :universes []
   :type (equality bool (replaces? (whole 5) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (replaces? (whole 5) (whole 3)))})

(def theorem-specs
  [slot-in-reservoir-replaces-spec replacement-within-reservoir-spec
   slot-beyond-reservoir-discards-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-reservoir-sampling
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
