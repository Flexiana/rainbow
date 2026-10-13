(ns rainbow.algorithms.proofs.ahof.cosine-similarity
  "AHoF Cosine Similarity: measure the similarity of two vectors by the cosine of
  the angle between them -- the dot product normalized by the product of their
  magnitudes,

      cosine dot-product magnitude-product = (a . b) / (|a| |b|).

  It is 1 for parallel vectors, 0 for orthogonal ones, and ignores magnitude, which
  is why it is the standard similarity for document term-vectors (TF-IDF), word and
  sentence embeddings, and recommendation. Proved native and axiom-free: the cosine
  as exact rational division of the dot product by the magnitude product; a worked
  similarity; and that identical unit-aligned vectors (dot product equal to the
  magnitude product) have cosine 1. The dot product and the magnitudes (a square
  root) are executable; what is proved is the normalized similarity.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cosine-similarity`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.division :as division]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-divide [l r]
  (function/app (function/const* 'nnrat/divide []) l r))
(defn- nnrat-equivalent [a b]
  (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- numerator-of [v]
  (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator-of [v]
  (function/app (function/const* 'nnrat/denominator []) v))
(defn- nat-multiply [a b]
  (function/app (function/const* 'nat/multiply []) a b))
(defn- equivalent-proof [a b]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (nat-multiply (numerator-of a) (denominator-of b))))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- cosine [dot-product magnitude-product]
  (function/app (function/const* 'cosine/similarity []) dot-product magnitude-product))

;; Definitions --------------------------------------------------------------

;; cosine dot magnitude-product = dot / magnitude-product
(def cosine-spec
  {:name 'cosine/similarity :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['dot-product nnrat] ['magnitude-product nnrat]]
                        (nnrat-divide 'dot-product 'magnitude-product))})

(def definition-specs [cosine-spec])

;; Theorems -----------------------------------------------------------------

;; Dot product 3, magnitude product 4 -> cosine 3/4.
(def cosine-example-spec
  {:name 'cosine/cosine-example :universes []
   :type (nnrat-equivalent (cosine (whole 3) (whole 4)) (fraction 3 3))
   :value (equivalent-proof (cosine (whole 3) (whole 4)) (fraction 3 3))})

;; Aligned vectors (dot product = magnitude product = 5) have cosine 1.
(def aligned-vectors-cosine-one-spec
  {:name 'cosine/aligned-vectors-cosine-one :universes []
   :type (nnrat-equivalent (cosine (whole 5) (whole 5)) (whole 1))
   :value (equivalent-proof (cosine (whole 5) (whole 5)) (whole 1))})

(def theorem-specs [cosine-example-spec aligned-vectors-cosine-one-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.division])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-cosine-similarity (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.cosine-similarity))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
