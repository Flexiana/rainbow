(ns rainbow.algorithms.proofs.ahof.sat
  "AHoF V50 SAT-based Bounded Model Checking: the system is unrolled k steps and
  encoded as a boolean formula in CNF; a counterexample exists iff the formula is
  satisfiable. The core evaluation is clause satisfaction under a truth
  assignment -- a clause (disjunction of literals) is satisfied when at least one
  of its literals is true:

      clause-satisfied? literals = fold or false literals.

  Proved native and axiom-free (a boolean fold via data/List.rec + logic/if-data,
  no rational arithmetic): the fold, its cons recurrence, and worked clauses. A
  full CNF formula is satisfied when every clause is; the SAT search itself and
  the unrolling encoding are executable concerns; what is proved here is the
  clause-satisfaction evaluation.

  Requires data/Bool, data/List.rec, and logic/if-data (all in the D63
  checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.sat`
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

;; or a b = if a then true else b
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- bool-or [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a true-value b))

(defn- clause-satisfied? [literals]
  (function/app (function/const* 'sat/clause-satisfied? []) literals))

;; Definitions --------------------------------------------------------------

;; clause-satisfied? literals = fold or false literals
(def clause-satisfied-spec
  {:name 'sat/clause-satisfied? :kind :definition :universes []
   :type (function/arrow list-bool bool)
   :value
   (function/lam
    [['literals list-bool]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     bool
     (function/lam [['ignored list-bool]] bool)
     false-value
     (function/lam [['head bool] ['tail list-bool] ['tail-sat bool]]
                   (bool-or 'head 'tail-sat))
     'literals))})

(def definition-specs [clause-satisfied-spec])

;; Theorems -----------------------------------------------------------------

(defn- clause [& literals]
  (reduce (fn [tail literal] (cons-bool literal tail)) nil-bool
          (reverse literals)))

;; The cons recurrence: a clause is satisfied if the head literal is true or the
;; rest is satisfied.
(def clause-cons-spec
  {:name 'sat/clause-cons :universes []
   :type (function/forall
          [['head bool] ['tail list-bool]]
          (equality bool
                    (clause-satisfied? (cons-bool 'head 'tail))
                    (bool-or 'head (clause-satisfied? 'tail))))
   :value (function/lam
           [['head bool] ['tail list-bool]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            bool (clause-satisfied? (cons-bool 'head 'tail))))})

;; A clause with a true literal is satisfied: [false, true, false] -> true.
(def clause-satisfiable-spec
  {:name 'sat/clause-satisfiable :universes []
   :type (equality bool
                   (clause-satisfied?
                    (clause false-value true-value false-value))
                   true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (clause-satisfied?
                         (clause false-value true-value false-value)))})

;; An all-false clause is unsatisfied: [false, false] -> false.
(def clause-unsatisfiable-spec
  {:name 'sat/clause-unsatisfiable :universes []
   :type (equality bool
                   (clause-satisfied? (clause false-value false-value))
                   false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool
                        (clause-satisfied? (clause false-value false-value)))})

;; The empty clause is unsatisfied (vacuously false).
(def clause-empty-spec
  {:name 'sat/clause-empty :universes []
   :type (equality bool (clause-satisfied? (clause)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (clause-satisfied? (clause)))})

(def theorem-specs
  [clause-cons-spec clause-satisfiable-spec clause-unsatisfiable-spec
   clause-empty-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-sat
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
