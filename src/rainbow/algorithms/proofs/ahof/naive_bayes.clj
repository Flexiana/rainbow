(ns rainbow.algorithms.proofs.ahof.naive-bayes
  "AHoF D-family Naive Bayes classifier: predict a class from features assumed
  conditionally independent given the class. The (unnormalized) posterior score of
  a class is its prior times the product of per-feature likelihoods,

      nb-score prior likelihoods = prior * (likelihood_1 * likelihood_2 * ...),

  and the predicted class is the argmax of these scores over the classes. Proved
  native and axiom-free: the class score composes the proved list-product fold
  over the feature likelihoods with the prior; a worked score; the prediction is
  the proved argmax-index fold over the class scores; a worked classification; and
  the certificate that the predicted class's score dominates every other class's
  (native nnrat/at-most). The likelihood/prior estimates are executable; what is
  proved is the score product and the argmax prediction.

  Requires list-product/product, argmax-index/argmax-index, nnrat/multiply,
  nnrat/at-most, audit/decide-nnrat-at-most, nnrat/decide-at-most-true-sound, and
  the D63 checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.naive-bayes`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.list-product :as list-product]
            [rainbow.algorithms.proofs.argmax-index :as argmax-index]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- data-nat [n]
  (nth (iterate succ (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- list-product-app [xs]
  (function/app (function/const* 'list-product/product []) xs))
(defn- argmax-index-app [xs]
  (function/app (function/const* 'argmax-index/argmax-index []) xs))
(defn- nb-score [prior likelihoods]
  (function/app (function/const* 'naive-bayes/score []) prior likelihoods))
(defn- classify [scores]
  (function/app (function/const* 'naive-bayes/classify []) scores))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; nb-score prior likelihoods = prior * product(likelihoods)
(def score-spec
  {:name 'naive-bayes/score :kind :definition :universes []
   :type (function/arrow nnrat list-nnrat nnrat)
   :value (function/lam [['prior nnrat] ['likelihoods list-nnrat]]
                        (nnrat-multiply 'prior (list-product-app 'likelihoods)))})

;; classify scores = argmax_c score(c)
(def classify-spec
  {:name 'naive-bayes/classify :kind :definition :universes []
   :type (function/arrow list-nnrat nat)
   :value (function/lam [['scores list-nnrat]] (argmax-index-app 'scores))})

(def definition-specs [score-spec classify-spec])

;; Theorems -----------------------------------------------------------------

;; Class score: prior 1 times feature likelihoods [2, 3] -> 6.
(def score-example-spec
  {:name 'naive-bayes/score-example :universes []
   :type (equality nnrat
                   (nb-score (whole 1) (nnrat-list (whole 2) (whole 3)))
                   (whole 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (nb-score (whole 1) (nnrat-list (whole 2) (whole 3))))})

;; Class scores [6, 4, 5]: the predicted class is 0 (highest score).
(def class-scores (nnrat-list (whole 6) (whole 4) (whole 5)))

(def classify-example-spec
  {:name 'naive-bayes/classify-example :universes []
   :type (equality nat (classify class-scores) (data-nat 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nat (classify class-scores))})

;; Certificate: the predicted class's score (6) dominates the others.
(def prediction-dominates-one-spec
  {:name 'naive-bayes/prediction-dominates-one :universes []
   :type (nnrat-at-most (whole 4) (whole 6))
   :value (at-most-proof (whole 4) (whole 6))})

(def prediction-dominates-two-spec
  {:name 'naive-bayes/prediction-dominates-two :universes []
   :type (nnrat-at-most (whole 5) (whole 6))
   :value (at-most-proof (whole 5) (whole 6))})

(def theorem-specs
  [score-example-spec classify-example-spec prediction-dominates-one-spec
   prediction-dominates-two-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      list-product/extend-environment
      argmax-index/extend-environment
      (support/extend-with :ahof-naive-bayes
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
