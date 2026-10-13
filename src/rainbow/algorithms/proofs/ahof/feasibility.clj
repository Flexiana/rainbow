(ns rainbow.algorithms.proofs.ahof.feasibility
  "Constraint feasibility checking (the conjunctive dual of the SAT clause and
  the model-checking companion of V50): a candidate is feasible when ALL of its
  constraints are satisfied. Given the per-constraint truth values, feasibility
  is their conjunction:

      feasible? constraints = fold and true constraints.

  Proved native and axiom-free (a boolean fold via data/List.rec + logic/if-data,
  no rational arithmetic): the fold, its cons recurrence, and worked constraint
  sets. This is the feasibility test underlying constraint-satisfaction search
  and the safety-specification check of bounded model checking (a run is a
  counterexample when it violates any constraint, i.e. is NOT feasible). The
  constraint evaluation itself is an executable concern; what is proved here is
  the conjunctive feasibility fold.

  Requires data/Bool, data/List.rec, and logic/if-data (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.feasibility`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def list-bool (function/app (function/const* 'data/List [type-level]) bool))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-bool [head tail]
  (function/app (function/const* 'data/cons [type-level]) bool head tail))
(def nil-bool (function/app (function/const* 'data/nil [type-level]) bool))

;; and a b = if a then b else false
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- bool-and [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))

(defn- feasible? [constraints]
  (function/app (function/const* 'feasibility/feasible? []) constraints))

;; Definitions --------------------------------------------------------------

;; feasible? constraints = fold and true constraints
(def feasible-spec
  {:name 'feasibility/feasible? :kind :definition :universes []
   :type (function/arrow list-bool bool)
   :value
   (function/lam
    [['constraints list-bool]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     bool
     (function/lam [['ignored list-bool]] bool)
     true-value
     (function/lam [['head bool] ['tail list-bool] ['tail-ok bool]]
                   (bool-and 'head 'tail-ok))
     'constraints))})

(def definition-specs [feasible-spec])

;; Theorems -----------------------------------------------------------------

(defn- constraints [& values]
  (reduce (fn [tail value] (cons-bool value tail)) nil-bool
          (reverse values)))

;; The cons recurrence: feasible if the head constraint holds and the rest are
;; feasible.
(def feasible-cons-spec
  {:name 'feasibility/feasible-cons :universes []
   :type (function/forall
          [['head bool] ['tail list-bool]]
          (equality bool
                    (feasible? (cons-bool 'head 'tail))
                    (bool-and 'head (feasible? 'tail))))
   :value (function/lam
           [['head bool] ['tail list-bool]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            bool (feasible? (cons-bool 'head 'tail))))})

;; All constraints satisfied -> feasible: [true, true] -> true.
(def all-satisfied-feasible-spec
  {:name 'feasibility/all-satisfied-feasible :universes []
   :type (equality bool
                   (feasible? (constraints true-value true-value))
                   true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (feasible? (constraints true-value true-value)))})

;; One violated constraint -> infeasible: [true, false, true] -> false.
(def one-violated-infeasible-spec
  {:name 'feasibility/one-violated-infeasible :universes []
   :type (equality bool
                   (feasible?
                    (constraints true-value false-value true-value))
                   false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (feasible?
                         (constraints true-value false-value true-value)))})

;; The unconstrained candidate is vacuously feasible: [] -> true.
(def unconstrained-feasible-spec
  {:name 'feasibility/unconstrained-feasible :universes []
   :type (equality bool (feasible? (constraints)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (feasible? (constraints)))})

(def theorem-specs
  [feasible-cons-spec all-satisfied-feasible-spec one-violated-infeasible-spec
   unconstrained-feasible-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-feasibility
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
