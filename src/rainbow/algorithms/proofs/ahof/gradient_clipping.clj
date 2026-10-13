(ns rainbow.algorithms.proofs.ahof.gradient-clipping
  "AHoF Gradient Clipping (clip-by-norm): stabilize the training of deep and
  recurrent networks by capping the gradient's magnitude, preventing the
  exploding-gradient problem where a single huge update destroys the model. When
  the gradient norm exceeds a threshold it is rescaled to exactly the threshold
  (preserving direction); otherwise it is left unchanged. The clipping decision
  is:

      clips? grad-norm threshold = decide (threshold <= grad-norm)

  and when clipping, the rescale factor is threshold / grad-norm. Proved native and
  axiom-free: the clip decision; that an oversized gradient is clipped; the
  certificate that a clipped gradient's norm really exceeded the threshold (native
  nnrat/at-most); and that a small gradient is left unclipped. The norm and the
  rescale are executable; what is proved is the clip decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gradient-clipping`
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

(defn- clips? [grad-norm threshold]
  (function/app (function/const* 'gradient-clipping/clips? []) grad-norm threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; clips? grad-norm threshold = decide (threshold <= grad-norm)
(def clips-spec
  {:name 'gradient-clipping/clips? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['grad-norm nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'grad-norm))})

(def definition-specs [clips-spec])

;; Theorems -----------------------------------------------------------------

;; A gradient of norm 7 exceeding the threshold 5 is clipped.
(def large-gradient-clipped-spec
  {:name 'gradient-clipping/large-gradient-clipped :universes []
   :type (equality bool (clips? (whole 7) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (clips? (whole 7) (whole 5)))})

;; Certificate: a clipped gradient's norm exceeded the threshold (5 <= 7).
(def clipped-exceeds-threshold-spec
  {:name 'gradient-clipping/clipped-exceeds-threshold :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

;; A gradient of norm 3 within the threshold 5 is left unclipped.
(def small-gradient-unclipped-spec
  {:name 'gradient-clipping/small-gradient-unclipped :universes []
   :type (equality bool (clips? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (clips? (whole 3) (whole 5)))})

(def theorem-specs
  [large-gradient-clipped-spec clipped-exceeds-threshold-spec
   small-gradient-unclipped-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-gradient-clipping
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
