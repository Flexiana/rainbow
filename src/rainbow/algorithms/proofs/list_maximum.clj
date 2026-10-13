(ns rainbow.algorithms.proofs.list-maximum
  "Maximum of a list of nonnegative rationals, as a native fold:

      list-maximum [x0, x1, ...] = max(x0, max(x1, ... max(xn, 0))).

  This is the reduction behind greedy best-of selection, maximum-fitness in
  evolutionary methods, Chebyshev / max-norm scalarization of multi-objective
  problems, and the max operator in value iteration over a finite action set. It
  is proved as a native List.rec fold of the decidable rational max
  (nnrat-max a b = if a <= b then b else a, built on logic/if-data over the
  decision audit/decide-nnrat-at-most). Proved axiom-free: the max operator, the
  fold, the empty and cons recurrences, and a worked maximum -- all reducing by
  reflexivity.

  Requires nnrat, audit/decide-nnrat-at-most, logic/if-data, and data/List.rec
  (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.list-maximum`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- if-nnrat [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                nnrat (condition decision) decision then-value else-value))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(def zero-nnrat (whole 0))

(defn- nnrat-max [a b]
  (function/app (function/const* 'list-maximum/nnrat-max []) a b))
(defn- list-maximum [xs]
  (function/app (function/const* 'list-maximum/maximum []) xs))

;; Definitions --------------------------------------------------------------

;; nnrat-max a b = if (a <= b) then b else a
(def nnrat-max-spec
  {:name 'list-maximum/nnrat-max :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (if-nnrat (decide-at-most 'a 'b) 'b 'a))})

;; list-maximum xs = fold nnrat-max 0 xs
(def maximum-spec
  {:name 'list-maximum/maximum :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value
   (function/lam
    [['xs list-nnrat]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored list-nnrat]] nnrat)
     zero-nnrat
     (function/lam [['head nnrat] ['tail list-nnrat] ['ih nnrat]]
                   (nnrat-max 'head 'ih))
     'xs))})

(def definition-specs [nnrat-max-spec maximum-spec])

;; Theorems -----------------------------------------------------------------

(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

;; max(3, 7) = 7.
(def nnrat-max-example-spec
  {:name 'list-maximum/nnrat-max-example :universes []
   :type (equality nnrat (nnrat-max (whole 3) (whole 7)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (nnrat-max (whole 3) (whole 7)))})

;; The maximum of the empty list is 0.
(def maximum-empty-spec
  {:name 'list-maximum/maximum-empty :universes []
   :type (equality nnrat (list-maximum (nnrat-list)) zero-nnrat)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (list-maximum (nnrat-list)))})

;; Cons recurrence: max of (h :: t) is max(h, max of t).
(def maximum-cons-spec
  {:name 'list-maximum/maximum-cons :universes []
   :type (function/forall
          [['head nnrat] ['tail list-nnrat]]
          (equality nnrat
                    (list-maximum (cons-nnrat 'head 'tail))
                    (nnrat-max 'head (list-maximum 'tail))))
   :value (function/lam
           [['head nnrat] ['tail list-nnrat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (list-maximum (cons-nnrat 'head 'tail))))})

;; Worked maximum: max [3, 7, 2] = 7.
(def maximum-example-spec
  {:name 'list-maximum/maximum-example :universes []
   :type (equality nnrat
                   (list-maximum (nnrat-list (whole 3) (whole 7) (whole 2)))
                   (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (list-maximum (nnrat-list (whole 3) (whole 7)
                                                  (whole 2))))})

(def theorem-specs
  [nnrat-max-example-spec maximum-empty-spec maximum-cons-spec
   maximum-example-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :list-maximum (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.list-maximum))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
