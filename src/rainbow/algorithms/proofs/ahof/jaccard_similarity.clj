(ns rainbow.algorithms.proofs.ahof.jaccard-similarity
  "AHoF Jaccard Similarity: measure how alike two SETS are by the size of their
  intersection over the size of their union,

      jaccard intersection-size union-size = |A intersect B| / |A union B|,

  a value in [0, 1] that is 1 for identical sets and 0 for disjoint ones. It
  underlies near-duplicate detection, document/shingle similarity (with MinHash),
  recommendation overlap, and clustering-quality indices. Proved native and
  axiom-free: the similarity as exact rational division of the intersection size
  by the union size; a worked similarity; and that identical sets (intersection =
  union) have similarity 1. The set intersection/union computations are
  executable; what is proved is the Jaccard ratio.

  Requires nnrat/divide (division is the rational-division capability, composed
  here), nnrat/equivalent, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.jaccard-similarity`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- jaccard [intersection-size union-size]
  (function/app (function/const* 'jaccard/similarity []) intersection-size union-size))

;; Definitions --------------------------------------------------------------

;; jaccard intersection union = intersection / union
(def jaccard-spec
  {:name 'jaccard/similarity :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['intersection-size nnrat] ['union-size nnrat]]
                        (nnrat-divide 'intersection-size 'union-size))})

(def definition-specs [jaccard-spec])

;; Theorems -----------------------------------------------------------------

;; Intersection 2, union 5 -> similarity 2/5.
(def jaccard-example-spec
  {:name 'jaccard/jaccard-example :universes []
   :type (nnrat-equivalent (jaccard (whole 2) (whole 5)) (fraction 2 4))
   :value (equivalent-proof (jaccard (whole 2) (whole 5)) (fraction 2 4))})

;; Identical sets (intersection = union = 4) have similarity 1.
(def identical-sets-similarity-one-spec
  {:name 'jaccard/identical-sets-similarity-one :universes []
   :type (nnrat-equivalent (jaccard (whole 4) (whole 4)) (whole 1))
   :value (equivalent-proof (jaccard (whole 4) (whole 4)) (whole 1))})

(def theorem-specs [jaccard-example-spec identical-sets-similarity-one-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (-> checked-environment
      division/extend-environment
      (support/extend-with :ahof-jaccard-similarity
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
