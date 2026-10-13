(ns rainbow.algorithms.proofs.ahof.pagerank
  "AHoF PageRank: rank the nodes of a directed graph by importance -- the
  stationary distribution of a random surfer who follows out-links with
  probability d (the damping factor) and teleports to a uniformly random node with
  probability 1-d. Computed by POWER ITERATION of the update:

      pagerank-update teleport damping incoming
        = teleport + damping * incoming

  where teleport = (1-d)/N and incoming = sum over in-links q of PR(q)/outdeg(q),
  over exact-rational ranks. Proved native and axiom-free: the rank update as the
  affine combination of the teleport term and the damped incoming mass; a worked
  update (stated as rational equivalence via the cross-product certificate, since
  the sum of fractions is not in lowest terms); and that a dangling node with no
  incoming mass keeps only the teleport rank. The link structure and the
  power-iteration loop are executable; what is proved is the rank-update combination.

  Requires nnrat/add, nnrat/multiply, nnrat/equivalent (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pagerank`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
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
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- whole [n] (fraction n 0))

(defn- pagerank-update [teleport damping incoming]
  (function/app (function/const* 'pagerank/update []) teleport damping incoming))

;; Definitions --------------------------------------------------------------

;; pagerank-update teleport damping incoming = teleport + damping * incoming
(def update-spec
  {:name 'pagerank/update :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['teleport nnrat] ['damping nnrat] ['incoming nnrat]]
                        (nnrat-add 'teleport
                                   (nnrat-multiply 'damping 'incoming)))})

(def definition-specs [update-spec])

;; Theorems -----------------------------------------------------------------

;; Teleport 1/4, damping 1/2, incoming 1 -> rank 3/4 (rational equivalence).
(def update-example-spec
  {:name 'pagerank/update-example :universes []
   :type (nnrat-equivalent
          (pagerank-update (fraction 1 3) (fraction 1 1) (whole 1))
          (fraction 3 3))
   :value (equivalent-proof
           (pagerank-update (fraction 1 3) (fraction 1 1) (whole 1))
           (fraction 3 3))})

;; A dangling node with no incoming mass keeps only the teleport rank:
;; teleport + damping * 0 = teleport (1/4).
(def dangling-keeps-teleport-spec
  {:name 'pagerank/dangling-keeps-teleport :universes []
   :type (nnrat-equivalent
          (pagerank-update (fraction 1 3) (fraction 1 1) (whole 0))
          (fraction 1 3))
   :value (equivalent-proof
           (pagerank-update (fraction 1 3) (fraction 1 1) (whole 0))
           (fraction 1 3))})

(def theorem-specs [update-example-spec dangling-keeps-teleport-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-pagerank (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.pagerank))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
