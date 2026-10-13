(ns rainbow.algorithms.proofs.ahof.christofides
  "AHoF Christofides Algorithm: the best-known polynomial APPROXIMATION for the
  metric Travelling Salesman Problem. It builds a minimum spanning tree, adds a
  minimum-weight perfect matching on the ODD-degree vertices (making all degrees
  even), forms an Eulerian circuit, and shortcuts repeated vertices (valid by the
  triangle inequality). Its classical guarantee (not proved here) is that the
  produced tour costs at most 3/2 times the optimal. A tour is accepted as
  within-bound when

      within-bound? tour-cost approximation-bound
        = decide (tour-cost <= approximation-bound)

  where approximation-bound = (3/2) * optimal-cost, over exact-rational costs.
  Proved native and axiom-free: the within-bound test, and worked instances with
  optimal cost 10 and bound 15 -- a tour of cost 13 is accepted; the certificate
  13 <= 15 as a native nnrat/at-most; and a tour of cost 17 is not accepted. The
  MST, matching, Euler tour, and shortcut steps are executable; what is proved is
  the bound decision at these instances, not the 3/2 approximation guarantee.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.christofides`
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

(defn- within-bound? [tour-cost approximation-bound]
  (function/app (function/const* 'christofides/within-bound? [])
                tour-cost approximation-bound))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; within-bound? tour-cost approximation-bound = decide (tour-cost <= bound)
(def within-bound-spec
  {:name 'christofides/within-bound? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['tour-cost nnrat] ['approximation-bound nnrat]]
                        (decide-at-most 'tour-cost 'approximation-bound))})

(def definition-specs [within-bound-spec])

;; Theorems -----------------------------------------------------------------

;; With optimal 10, the 3/2 bound is 15; a Christofides tour of cost 13 is within
;; the guarantee.
(def tour-within-guarantee-spec
  {:name 'christofides/tour-within-guarantee :universes []
   :type (equality bool (within-bound? (whole 13) (whole 15))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-bound? (whole 13) (whole 15)))})

;; Worked certificate: 13 <= 15.
(def tour-at-most-bound-spec
  {:name 'christofides/tour-at-most-bound :universes []
   :type (nnrat-at-most (whole 13) (whole 15))
   :value (at-most-proof (whole 13) (whole 15))})

;; A tour exceeding the 3/2 bound (cost 17 > bound 15) is not certified.
(def tour-over-bound-rejected-spec
  {:name 'christofides/tour-over-bound-rejected :universes []
   :type (equality bool (within-bound? (whole 17) (whole 15))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (within-bound? (whole 17) (whole 15)))})

(def theorem-specs
  [tour-within-guarantee-spec tour-at-most-bound-spec tour-over-bound-rejected-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-christofides
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
