(ns rainbow.algorithms.proofs.branch-and-bound
  "AHoF D34 / O-family Branch and Bound: the bounding test that turns exhaustive
  enumeration into a pruned search. A node carries an optimistic bound on the
  best objective reachable in its subtree; when that bound is already dominated
  by the incumbent (the best solution found so far), the whole subtree is pruned
  because it cannot contain a better solution.

  The pruning predicate is the decidable rational comparison

      dominated? bound incumbent = decide (bound <= incumbent)

  Proved native and axiom-free: worked instances on concrete values -- bound 3
  against incumbent 5 is dominated; the worked certificate 3 <= 5 (a native
  `nnrat/at-most`, obtained from the decision computing to true); and bound 7
  against incumbent 5 is not dominated. The branching strategy and the bound
  function are executable concerns; what is proved here is the pruning predicate
  at these instances. That pruning never discards a better solution is the
  classical soundness of branch and bound and is not proved here.

  Requires `nnrat/at-most`, `audit/decide-nnrat-at-most`, and
  `nnrat/decide-at-most-true-sound` in the environment (all carried by the D63
  checkpoint, as used by the geometric-convergence bounds).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.branch-and-bound`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- dominated? [bound incumbent]
  (function/app (function/const* 'branch-and-bound/dominated? [])
                bound incumbent))

;; A proof of `nnrat/at-most a b` via the decidable comparison computing to true.
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; dominated? bound incumbent = decide (bound <= incumbent)
(def dominated-spec
  {:name 'branch-and-bound/dominated? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['bound nnrat] ['incumbent nnrat]]
                        (decide-at-most 'bound 'incumbent))})

(def definition-specs [dominated-spec])

;; Theorems -----------------------------------------------------------------

;; A node with bound 3 against incumbent 5 is flagged dominated (3 <= 5 decides
;; true), so its subtree is pruned.
(def prunes-dominated-node-spec
  {:name 'branch-and-bound/prunes-dominated-node :universes []
   :type (equality bool (dominated? (whole 3) (whole 5))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (dominated? (whole 3) (whole 5)))})

;; Worked certificate: bound 3 <= incumbent 5 (native at-most).
(def pruned-bound-dominated-spec
  {:name 'branch-and-bound/pruned-bound-dominated :universes []
   :type (nnrat-at-most (whole 3) (whole 5))
   :value (at-most-proof (whole 3) (whole 5))})

;; A node whose bound 7 exceeds the incumbent 5 is not dominated (7 <= 5 decides
;; false), so it must be explored rather than pruned.
(def explores-promising-node-spec
  {:name 'branch-and-bound/explores-promising-node :universes []
   :type (equality bool (dominated? (whole 7) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (dominated? (whole 7) (whole 5)))})

(def theorem-specs
  [prunes-dominated-node-spec pruned-bound-dominated-spec
   explores-promising-node-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :branch-and-bound (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.branch-and-bound))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
