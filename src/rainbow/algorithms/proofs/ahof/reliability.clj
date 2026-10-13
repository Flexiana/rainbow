(ns rainbow.algorithms.proofs.ahof.reliability
  "AHoF V-family Series-System Reliability (reliability block diagram): a series
  system works only if EVERY component works, so with independent components its
  reliability is the product of the component reliabilities,

      series-reliability [r0, r1, ...] = r0 * r1 * ...

  and the design meets its reliability requirement when this product is at least a
  target threshold. Proved native and axiom-free: the series reliability is the
  proved list-product fold over the component reliabilities; a worked reliability;
  the requirement decision; the certificate that a passing design really meets the
  target (threshold <= reliability as native nnrat/at-most); and that a system
  below target fails the requirement. The component reliability estimates are
  executable; what is proved is the series-reliability product and the requirement
  decision.

  Requires list-product/product, audit/decide-nnrat-at-most, nnrat/at-most,
  nnrat/decide-at-most-true-sound, and the D63 checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.reliability`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.list-product :as list-product]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

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

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- list-product-app [xs]
  (function/app (function/const* 'list-product/product []) xs))
(defn- series-reliability [rs]
  (function/app (function/const* 'reliability/series []) rs))
(defn- meets-requirement? [reliability threshold]
  (function/app (function/const* 'reliability/meets-requirement? [])
                reliability threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; series-reliability rs = product(rs)
(def series-spec
  {:name 'reliability/series :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value (function/lam [['rs list-nnrat]] (list-product-app 'rs))})

;; meets-requirement? reliability threshold = decide (threshold <= reliability)
(def meets-spec
  {:name 'reliability/meets-requirement? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['reliability nnrat] ['threshold nnrat]]
                        (decide-at-most 'threshold 'reliability))})

(def definition-specs [series-spec meets-spec])

;; Theorems -----------------------------------------------------------------

;; Two components each 1/2 reliable -> series reliability 1/4.
(def series-example-spec
  {:name 'reliability/series-example :universes []
   :type (equality nnrat
                   (series-reliability (nnrat-list (fraction 1 1) (fraction 1 1)))
                   (fraction 1 3))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (series-reliability
                         (nnrat-list (fraction 1 1) (fraction 1 1))))})

;; A perfect series (all components reliability 1) has reliability 1.
(def perfect-series-spec
  {:name 'reliability/perfect-series :universes []
   :type (equality nnrat
                   (series-reliability (nnrat-list (whole 1) (whole 1) (whole 1)))
                   (whole 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (series-reliability
                         (nnrat-list (whole 1) (whole 1) (whole 1))))})

;; A design with reliability 3/4 meets a target of 1/2.
(def meets-target-spec
  {:name 'reliability/meets-target :universes []
   :type (equality bool
                   (meets-requirement? (fraction 3 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (meets-requirement? (fraction 3 3) (fraction 1 1)))})

;; Certificate: a passing design's reliability is at least the target (1/2 <= 3/4).
(def passing-meets-threshold-spec
  {:name 'reliability/passing-meets-threshold :universes []
   :type (nnrat-at-most (fraction 1 1) (fraction 3 3))
   :value (at-most-proof (fraction 1 1) (fraction 3 3))})

(def theorem-specs
  [series-example-spec perfect-series-spec meets-target-spec
   passing-meets-threshold-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.list-product])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-reliability (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.reliability))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
