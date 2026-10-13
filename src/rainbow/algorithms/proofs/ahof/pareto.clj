(ns rainbow.algorithms.proofs.ahof.pareto
  "AHoF multiobjective optimization -- Pareto dominance, the partial order that
  defines the Pareto front. For a minimization problem with two objectives, a
  solution a weakly dominates b when a is no worse than b in every objective:

      dominates? a1 a2 b1 b2 = (a1 <= b1) and (a2 <= b2)

  expressed as nested if-data over the decidable rational order (no boolean
  connective needed). Proved native and axiom-free, as worked instances: (2,3)
  dominates (5,4); the worked certificates 2 <= 5 and 3 <= 4 (native
  nnrat/at-most); and (6,3) does not dominate (5,4). The soundness of the test for
  all inputs, and of a Pareto-front filter built on it, is not proved here.
  Extending to k objectives and extracting the non-dominated front are executable
  concerns.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.pareto`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- if-bool [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition decision) decision then-value else-value))

(defn- dominates? [a1 a2 b1 b2]
  (function/app (function/const* 'pareto/dominates? []) a1 a2 b1 b2))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; dominates? a1 a2 b1 b2 = (a1 <= b1) and (a2 <= b2)
(def dominates-spec
  {:name 'pareto/dominates? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat bool)
   :value (function/lam [['a1 nnrat] ['a2 nnrat] ['b1 nnrat] ['b2 nnrat]]
                        (if-bool (decide-at-most 'a1 'b1)
                                 (if-bool (decide-at-most 'a2 'b2)
                                          true-value false-value)
                                 false-value))})

(def definition-specs [dominates-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; (2,3) dominates (5,4): no worse in both objectives.
(def dominates-example-spec
  {:name 'pareto/dominates-example :universes []
   :type (equality bool
                   (dominates? (whole 2) (whole 3) (whole 5) (whole 4))
                   true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (dominates? (whole 2) (whole 3) (whole 5) (whole 4)))})

;; Worked certificate in objective 1 for the example above: 2 <= 5.
(def dominated-in-objective-1-spec
  {:name 'pareto/dominated-in-objective-1 :universes []
   :type (nnrat-at-most (whole 2) (whole 5))
   :value (at-most-proof (whole 2) (whole 5))})

;; Worked certificate in objective 2 for the example above: 3 <= 4.
(def dominated-in-objective-2-spec
  {:name 'pareto/dominated-in-objective-2 :universes []
   :type (nnrat-at-most (whole 3) (whole 4))
   :value (at-most-proof (whole 3) (whole 4))})

;; Non-dominance: (6,3) does not dominate (5,4) -- worse in objective 1.
(def non-dominance-example-spec
  {:name 'pareto/non-dominance-example :universes []
   :type (equality bool
                   (dominates? (whole 6) (whole 3) (whole 5) (whole 4))
                   false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (dominates? (whole 6) (whole 3) (whole 5) (whole 4)))})

(def theorem-specs
  [dominates-example-spec dominated-in-objective-1-spec
   dominated-in-objective-2-spec non-dominance-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-pareto
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
