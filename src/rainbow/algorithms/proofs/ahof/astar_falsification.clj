(ns rainbow.algorithms.proofs.ahof.astar-falsification
  "AHoF V18 A* for Falsification: search the space of system behaviours for a
  specification violation using A*, ordering the frontier by the f-cost f = g + h (the
  cost so far plus an admissible heuristic to a likely violation) and always expanding
  the lowest-f node:

      priority       g h   = g + h
      prefers-lower? f0 f1 = decide (f0 <= f1)
      expand-value   f0 f1 = if (f0 <= f1) then f0 else f1   (the lower f-cost)

  over exact rationals. Proved native and axiom-free: the priority sum (1/2 + 1/4 =
  3/4 by cross-product equivalence), the min-f frontier selection, and the preference
  decision. Requires nnrat/add, audit/decide-nnrat-at-most, logic/if-data,
  nnrat/equivalent (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.astar-falsification`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def one-quarter (make-rational 1 3))
(def one-half (make-rational 1 1))
(def three-quarters (make-rational 3 3))
(def whole-1 (make-rational 1 0))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- priority [g h] (function/app (function/const* 'astar-fal/priority []) g h))
(defn- prefers-lower? [f0 f1] (function/app (function/const* 'astar-fal/prefers-lower? []) f0 f1))
(defn- expand-value [f0 f1] (function/app (function/const* 'astar-fal/expand-value []) f0 f1))

(def priority-spec
  {:name 'astar-fal/priority :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['g nnrat] ['h nnrat]] (nnrat-add 'g 'h))})

(def prefers-lower-spec
  {:name 'astar-fal/prefers-lower? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['f0 nnrat] ['f1 nnrat]] (decide-at-most 'f0 'f1))})

(def expand-value-spec
  {:name 'astar-fal/expand-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['f0 nnrat] ['f1 nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'f0 'f1))
                                      (decide-at-most 'f0 'f1) 'f0 'f1))})

(def worked-priority-spec
  {:name 'astar-fal/worked-priority :kind :definition :universes [] :type nnrat
   :value (priority one-half one-quarter)})

(def definition-specs [priority-spec prefers-lower-spec expand-value-spec worked-priority-spec])

;; f = g + h : 1/2 + 1/4 = 3/4.
(def priority-is-three-quarters-spec
  {:name 'astar-fal/priority-is-three-quarters :universes []
   :type (nnrat-equivalent (function/const* 'astar-fal/worked-priority []) three-quarters)
   :value (equivalent-cross (function/const* 'astar-fal/worked-priority []) three-quarters)})

;; The frontier expands the lower-f node: min(3/4, 1) = 3/4.
(def expands-lower-f-spec
  {:name 'astar-fal/expands-lower-f :universes []
   :type (equality nnrat (expand-value three-quarters whole-1) three-quarters)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (expand-value three-quarters whole-1))})

;; The lower-f node 3/4 is preferred over 1.
(def prefers-lower-example-spec
  {:name 'astar-fal/prefers-lower-example :universes []
   :type (equality bool (prefers-lower? three-quarters whole-1) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-lower? three-quarters whole-1))})

(def theorem-specs
  [priority-is-three-quarters-spec expands-lower-f-spec prefers-lower-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-astar-falsification (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.astar-falsification))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
