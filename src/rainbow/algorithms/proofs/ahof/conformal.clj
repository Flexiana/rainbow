(ns rainbow.algorithms.proofs.ahof.conformal
  "AHoF Conformal Prediction: a distribution-free method that turns any point
  predictor into set-valued predictions with a finite-sample coverage guarantee.
  From a calibration set it computes a nonconformity-score threshold q (the
  (1-alpha)-empirical-quantile of calibration scores); a candidate label y is
  included in the prediction set for a test point exactly when its nonconformity
  score is at most the threshold:

      in-prediction-set? score q = decide (score <= q)

  over exact-rational scores. Proved native and axiom-free: the inclusion test;
  worked instances with threshold 5 -- a label scoring 3 is included; the
  certificate 3 <= 5 as a native nnrat/at-most; and a label scoring 7 is excluded.
  The 1-alpha marginal coverage guarantee (the classical exchangeability argument)
  is not proved here. The base predictor, the score function, and the empirical
  quantile are executable; what is proved is the inclusion decision at these
  instances.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.conformal`
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

(defn- in-set? [score q]
  (function/app (function/const* 'conformal/in-prediction-set? []) score q))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; in-prediction-set? score q = decide (score <= q)
(def in-set-spec
  {:name 'conformal/in-prediction-set? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['score nnrat] ['q nnrat]]
                        (decide-at-most 'score 'q))})

(def definition-specs [in-set-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A label scoring 3 with threshold q = 5 is in the prediction set.
(def includes-conforming-spec
  {:name 'conformal/includes-conforming :universes []
   :type (equality bool (in-set? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-set? (whole 3) (whole 5)))})

;; Worked certificate: 3 <= 5.
(def included-within-threshold-spec
  {:name 'conformal/included-within-threshold :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A label scoring 7 (above threshold 5) is excluded from the prediction set.
(def excludes-nonconforming-spec
  {:name 'conformal/excludes-nonconforming :universes []
   :type (equality bool (in-set? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (in-set? (whole 7) (whole 5)))})

(def theorem-specs
  [includes-conforming-spec included-within-threshold-spec
   excludes-nonconforming-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-conformal
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
