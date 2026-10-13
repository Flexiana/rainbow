(ns rainbow.algorithms.proofs.ahof.gini-impurity
  "AHoF Gini Impurity: the node-purity criterion used by CART decision trees (and
  a cheaper alternative to entropy). For a node with class proportions p_i, the
  Gini impurity is 1 - sum p_i^2 -- the probability that two randomly drawn labels
  differ; it is 0 for a pure node (one class) and maximal for a uniform mix. A
  split is chosen to MINIMIZE the weighted child impurity, so comparing two
  candidate splits reduces to comparing their impurities:

      purer-split? impurity-a impurity-b = decide (impurity-a <= impurity-b)

  (the lower-impurity split is the purer, better one), over exact-rational
  impurities. Proved native and axiom-free: the purity-comparison test; that the
  lower-impurity split is preferred; the certificate that a chosen split's impurity
  is at most the alternative's (native nnrat/at-most) -- greedy purity maximization;
  and that a higher-impurity split is not preferred. The 1 - sum p_i^2 computation
  is executable; what is proved is the purer-split comparison.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.gini-impurity`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
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
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- purer-split? [impurity-a impurity-b]
  (function/app (function/const* 'gini-impurity/purer-split? []) impurity-a impurity-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; purer-split? impurity-a impurity-b = decide (impurity-a <= impurity-b)
(def purer-split-spec
  {:name 'gini-impurity/purer-split? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['impurity-a nnrat] ['impurity-b nnrat]]
                        (decide-at-most 'impurity-a 'impurity-b))})

(def definition-specs [purer-split-spec])

;; Theorems -----------------------------------------------------------------

;; A split with impurity 1/4 is purer (better) than one with impurity 1/2.
(def lower-impurity-preferred-spec
  {:name 'gini-impurity/lower-impurity-preferred :universes []
   :type (equality bool (purer-split? (fraction 1 3) (fraction 1 1))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (purer-split? (fraction 1 3) (fraction 1 1)))})

;; Certificate: a chosen split's impurity is at most the alternative's
;; (1/4 <= 1/2) -- greedy purity maximization.
(def chosen-split-purer-spec
  {:name 'gini-impurity/chosen-split-purer :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

;; A higher-impurity split (1/2) is not preferred over a purer one (1/4).
(def higher-impurity-not-preferred-spec
  {:name 'gini-impurity/higher-impurity-not-preferred :universes []
   :type (equality bool (purer-split? (fraction 1 1) (fraction 1 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (purer-split? (fraction 1 1) (fraction 1 3)))})

(def theorem-specs
  [lower-impurity-preferred-spec chosen-split-purer-spec
   higher-impurity-not-preferred-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-gini-impurity (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.gini-impurity))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
