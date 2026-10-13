(ns rainbow.algorithms.proofs.list-product
  "Product of a list of nonnegative rationals, as a native fold:

      list-product [x0, x1, ...] = x0 * x1 * ... * xn    (empty product = 1).

  This is the reduction behind joint probability of independent events, the
  likelihood of an i.i.d. sample (a product of per-datum likelihoods, as in naive
  Bayes), series-system reliability (a product of component reliabilities), and
  any multiplicative accumulation. It is proved as a native List.rec fold of
  nnrat/multiply from the multiplicative identity nnrat/one. Proved axiom-free:
  the fold, the empty and cons recurrences, and a worked product -- all reducing
  by reflexivity.

  Requires nnrat, nnrat/multiply, nnrat/one, and data/List.rec (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.list-product`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- list-product [xs]
  (function/app (function/const* 'list-product/product []) xs))

;; Definitions --------------------------------------------------------------

;; list-product xs = fold nnrat-multiply 1 xs
(def product-spec
  {:name 'list-product/product :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value
   (function/lam
    [['xs list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nnrat)
     nnrat-one
     (function/lam [['head nnrat] ['tail list-nnrat] ['ih nnrat]]
                   (nnrat-multiply 'head 'ih))
     'xs))})

(def definition-specs [product-spec])

;; Theorems -----------------------------------------------------------------

;; The empty product is 1 (the multiplicative identity).
(def product-empty-spec
  {:name 'list-product/product-empty :universes []
   :type (equality nnrat (list-product (nnrat-list)) nnrat-one)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (list-product (nnrat-list)))})

;; Cons recurrence: product of (h :: t) is h * (product of t).
(def product-cons-spec
  {:name 'list-product/product-cons :universes []
   :type (function/forall
          [['head nnrat] ['tail list-nnrat]]
          (equality nnrat
                    (list-product (cons-nnrat 'head 'tail))
                    (nnrat-multiply 'head (list-product 'tail))))
   :value (function/lam
           [['head nnrat] ['tail list-nnrat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (list-product (cons-nnrat 'head 'tail))))})

;; Worked product: [2, 3, 2] -> 12.
(def product-example-spec
  {:name 'list-product/product-example :universes []
   :type (equality nnrat
                   (list-product (nnrat-list (whole 2) (whole 3) (whole 2)))
                   (whole 12))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (list-product (nnrat-list (whole 2) (whole 3)
                                                  (whole 2))))})

(def theorem-specs
  [product-empty-spec product-cons-spec product-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :list-product
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
