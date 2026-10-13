(ns rainbow.algorithms.proofs.ahof.svm
  "AHoF Support Vector Machine (linear, hard-margin classification): find the
  hyperplane that separates two classes with the MAXIMUM margin, then classify a
  point by which side it falls on. Training maximizes the margin subject to every
  example satisfying y_i (w.x_i - b) >= 1; at prediction time, a point is assigned
  the positive class when its functional margin reaches the decision boundary:

      classify-positive? margin threshold = decide (threshold <= margin)

  where margin = w.x - b and threshold = 0 for the decision, or 1 for the
  confident-margin band, over exact-rational margins. Proved native and axiom-free:
  the side-of-hyperplane decision; that a point on the positive side is classified
  positive; the certificate that a point classified confident-positive really has
  functional margin at least 1 (native nnrat/at-most) -- the max-margin constraint;
  and that a point below the boundary is classified negative. The weight vector,
  bias, and dot product are executable; what is proved is the margin decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.svm`
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

(defn- classify-positive? [margin threshold]
  (function/app (function/const* 'svm/classify-positive? []) margin threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; classify-positive? margin threshold = decide (threshold <= margin)
(def classify-positive-spec
  {:name 'svm/classify-positive? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['margin nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'margin))})

(def definition-specs [classify-positive-spec])

;; Theorems -----------------------------------------------------------------

;; A point with margin 2 on the positive side of the boundary (threshold 0).
(def positive-side-classified-positive-spec
  {:name 'svm/positive-side-classified-positive :universes []
   :type (equality bool (classify-positive? (whole 2) (whole 0))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (classify-positive? (whole 2) (whole 0)))})

;; Max-margin certificate: a confident-positive point has functional margin at
;; least 1 (1 <= 2), satisfying the SVM constraint y(w.x - b) >= 1.
(def confident-margin-at-least-one-spec
  {:name 'svm/confident-margin-at-least-one :universes []
   :type (nnrat-at-most (whole 1) (whole 2))
   :value (at-most-proof (whole 1) (whole 2))})

;; A point with margin 0 below the confident band (threshold 1) is not
;; confidently positive (it lies inside the margin).
(def inside-margin-not-confident-spec
  {:name 'svm/inside-margin-not-confident :universes []
   :type (equality bool (classify-positive? (whole 0) (whole 1))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (classify-positive? (whole 0) (whole 1)))})

(def theorem-specs
  [positive-side-classified-positive-spec confident-margin-at-least-one-spec
   inside-margin-not-confident-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-svm
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
