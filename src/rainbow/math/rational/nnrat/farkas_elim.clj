(ns rainbow.math.rational.nnrat.farkas-elim
  "A bounded first Fourier--Motzkin milestone over exact nonnegative rationals.

  This module represents a normalized finite one-variable constraint system with
  two lower bounds and two upper bounds as proof data:

      l1 <= v,  l2 <= v,  v <= u1,  v <= u2.

  Eliminating v leaves the single lattice inequality

      max(l1,l2) <= min(u1,u2),

  equivalent to the four pairwise lower/upper comparisons.  The main theorem
  proves, constructively and in both directions, that the reduced proposition is
  equivalent to existence of a value satisfying the original system.  In the
  extension direction the witness is max(l1,l2); reduced feasibility and the
  min/max lattice laws place it below both upper bounds.

  Scope: this is the fixed two-lower/two-upper normalized core, rather than list-
  sized coefficient-bearing inequalities.  The next step is list induction that
  folds lower bounds with max and upper bounds with min, followed by normalization
  of nonzero target-variable coefficients into these bound predicates.  Native
  and axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- minimum [left right]
  (function/app (function/const* 'minmax/min []) left right))

(defn- maximum [left right]
  (function/app (function/const* 'minmax/max []) left right))

(defn- system [l1 l2 u1 u2 value]
  (function/app
   (function/const* 'nnrat/farkas-elim-two-lower-two-upper-system [])
   l1 l2 u1 u2 value))

(defn- reduced-system [l1 l2 u1 u2]
  (function/app
   (function/const* 'nnrat/farkas-elim-two-lower-two-upper-reduced [])
   l1 l2 u1 u2))

(defn- solvable [l1 l2 u1 u2]
  (function/app
   (function/const* 'nnrat/farkas-elim-two-lower-two-upper-solvable [])
   l1 l2 u1 u2))

(defn- conjoin [left right left-proof right-proof]
  (function/app (function/const* 'proposition/conjoin [])
                left right left-proof right-proof))

(defn- left-conjunct [left right both]
  (function/app (function/const* 'proposition/left []) left right both))

(defn- right-conjunct [left right both]
  (function/app (function/const* 'proposition/right []) left right both))

(defn- at-most-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/at-most-transitive [])
                left middle right first second))

(defn- min-lower-left [left right]
  (function/app (function/const* 'minmax/min-lower-left []) left right))

(defn- min-lower-right [left right]
  (function/app (function/const* 'minmax/min-lower-right []) left right))

(defn- max-upper-left [left right]
  (function/app (function/const* 'minmax/max-upper-left []) left right))

(defn- max-upper-right [left right]
  (function/app (function/const* 'minmax/max-upper-right []) left right))

(defn- at-most-min [low left right low-left low-right]
  (function/app (function/const* 'minmax/at-most-min [])
                low left right low-left low-right))

(defn- at-most-max [left right high left-high right-high]
  (function/app (function/const* 'minmax/at-most-max [])
                left right high left-high right-high))

(def system-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-system
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat] ['value nnrat]]
    (proposition/conjunction
     (proposition/conjunction (at-most 'l1 'value) (at-most 'l2 'value))
     (proposition/conjunction (at-most 'value 'u1) (at-most 'value 'u2))))})

(def reduced-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-reduced
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]]
    (at-most (maximum 'l1 'l2) (minimum 'u1 'u2)))})

(def solvable-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-solvable
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat 'Prop)
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]]
    (proposition/existence
     type-level nnrat
     (function/lam [['value nnrat]] (system 'l1 'l2 'u1 'u2 'value))))})

(def definition-specs [system-spec reduced-spec solvable-spec])

(def extends-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-extends
   :universes []
   :type
   (function/forall
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]
     ['reduced-feasible (reduced-system 'l1 'l2 'u1 'u2)]]
    (solvable 'l1 'l2 'u1 'u2))
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]
     ['reduced-feasible (reduced-system 'l1 'l2 'u1 'u2)]]
    (let [value (maximum 'l1 'l2)
          min-upper (minimum 'u1 'u2)
          lower-left (at-most 'l1 value)
          lower-right (at-most 'l2 value)
          upper-left (at-most value 'u1)
          upper-right (at-most value 'u2)
          lower-pair (proposition/conjunction lower-left lower-right)
          upper-pair (proposition/conjunction upper-left upper-right)
          system-predicate
          (function/lam [['candidate nnrat]]
                        (system 'l1 'l2 'u1 'u2 'candidate))
          value-at-most-u1
          (at-most-transitive value min-upper 'u1
                              'reduced-feasible
                              (min-lower-left 'u1 'u2))
          value-at-most-u2
          (at-most-transitive value min-upper 'u2
                              'reduced-feasible
                              (min-lower-right 'u1 'u2))
          satisfies
          (conjoin
           lower-pair upper-pair
           (conjoin lower-left lower-right
                    (max-upper-left 'l1 'l2)
                    (max-upper-right 'l1 'l2))
           (conjoin upper-left upper-right
                    value-at-most-u1 value-at-most-u2))]
      (function/app (function/const* 'proposition/witness [type-level])
                    nnrat system-predicate value satisfies)))})

(def projects-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-projects
   :universes []
   :type
   (function/forall
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]
     ['solution (solvable 'l1 'l2 'u1 'u2)]]
    (reduced-system 'l1 'l2 'u1 'u2))
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]
     ['solution (solvable 'l1 'l2 'u1 'u2)]]
    (let [lower-left (fn [value] (at-most 'l1 value))
          lower-right (fn [value] (at-most 'l2 value))
          upper-left (fn [value] (at-most value 'u1))
          upper-right (fn [value] (at-most value 'u2))
          lower-pair
          (fn [value] (proposition/conjunction
                       (lower-left value) (lower-right value)))
          upper-pair
          (fn [value] (proposition/conjunction
                       (upper-left value) (upper-right value)))
          system-predicate
          (function/lam [['value nnrat]] (system 'l1 'l2 'u1 'u2 'value))]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nnrat system-predicate (reduced-system 'l1 'l2 'u1 'u2) 'solution
       (function/lam
        [['value nnrat]
         ['satisfies (system 'l1 'l2 'u1 'u2 'value)]]
        (let [lowers (left-conjunct (lower-pair 'value)
                                    (upper-pair 'value) 'satisfies)
              uppers (right-conjunct (lower-pair 'value)
                                     (upper-pair 'value) 'satisfies)
              l1-at-most-value
              (left-conjunct (lower-left 'value) (lower-right 'value) lowers)
              l2-at-most-value
              (right-conjunct (lower-left 'value) (lower-right 'value) lowers)
              value-at-most-u1
              (left-conjunct (upper-left 'value) (upper-right 'value) uppers)
              value-at-most-u2
              (right-conjunct (upper-left 'value) (upper-right 'value) uppers)
              max-at-most-value
              (at-most-max 'l1 'l2 'value l1-at-most-value l2-at-most-value)
              value-at-most-min
              (at-most-min 'value 'u1 'u2 value-at-most-u1 value-at-most-u2)]
          (at-most-transitive (maximum 'l1 'l2) 'value
                              (minimum 'u1 'u2)
                              max-at-most-value value-at-most-min))))))})

(def solvable-iff-spec
  {:name 'nnrat/farkas-elim-two-lower-two-upper-solvable-iff
   :universes []
   :type
   (function/forall
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]]
    (proposition/equivalence
     (reduced-system 'l1 'l2 'u1 'u2)
     (solvable 'l1 'l2 'u1 'u2)))
   :value
   (function/lam
    [['l1 nnrat] ['l2 nnrat] ['u1 nnrat] ['u2 nnrat]]
    (let [reduced-prop (reduced-system 'l1 'l2 'u1 'u2)
          solvable-prop (solvable 'l1 'l2 'u1 'u2)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       reduced-prop solvable-prop
       (function/lam
        [['reduced-feasible reduced-prop]]
        (function/app
         (function/const*
          'nnrat/farkas-elim-two-lower-two-upper-extends [])
         'l1 'l2 'u1 'u2 'reduced-feasible))
       (function/lam
        [['solution solvable-prop]]
        (function/app
         (function/const*
          'nnrat/farkas-elim-two-lower-two-upper-projects [])
         'l1 'l2 'u1 'u2 'solution)))))})

(def theorem-specs [extends-spec projects-spec solvable-iff-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-farkas-elim (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.farkas-elim))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
