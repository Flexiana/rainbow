(ns rainbow.algorithms.proofs.ahof.pc
  "AHoF D16 PC Algorithm: constraint-based Bayesian-network structure learning.
  Starting from the complete graph, PC removes an edge X-Y whenever a conditional
  independence test finds X and Y independent given some conditioning set. The
  independence test compares a dependence statistic against a significance
  threshold:

      independent? statistic threshold = decide (statistic <= threshold)

  over the exact-rational statistic (a chi-square / partial-correlation value).
  Proved native and axiom-free, as worked instances: statistic 2 against
  threshold 5 declares independence; the worked certificate 2 <= 5 (native
  nnrat/at-most); and statistic 8 against threshold 5 keeps the edge. The
  soundness of PC's edge removal is classical and not proved here. The statistic
  computation, the conditioning-set search, and the edge-orientation phase are
  executable concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pc`
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

(defn- independent? [statistic threshold]
  (function/app (function/const* 'pc/independent? []) statistic threshold))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; independent? statistic threshold = decide (statistic <= threshold)
(def independent-spec
  {:name 'pc/independent? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['statistic nnrat] ['threshold nnrat]]
                        (decide-at-most 'statistic 'threshold))})

(def definition-specs [independent-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; A low dependence statistic (2 <= threshold 5) declares independence; edge cut.
(def declares-independence-spec
  {:name 'pc/declares-independence :universes []
   :type (equality bool (independent? (whole 2) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (independent? (whole 2) (whole 5)))})

;; Worked certificate for the independence above: 2 <= 5.
(def independence-is-sound-spec
  {:name 'pc/independence-is-sound :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; A strongly dependent pair (8 > 5) is kept -- its edge remains.
(def keeps-dependent-edge-spec
  {:name 'pc/keeps-dependent-edge :universes []
   :type (equality bool (independent? (whole 8) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (independent? (whole 8) (whole 5)))})

(def theorem-specs
  [declares-independence-spec independence-is-sound-spec
   keeps-dependent-edge-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-pc (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.pc))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
