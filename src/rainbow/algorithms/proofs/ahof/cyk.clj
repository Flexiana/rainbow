(ns rainbow.algorithms.proofs.ahof.cyk
  "AHoF CYK Algorithm (Cocke-Younger-Kasami): decide whether a string is generated
  by a context-free grammar in Chomsky Normal Form, in O(n^3 * |G|), by dynamic
  programming over substrings. A cell for a span holds the nonterminals that derive
  it; a rule A -> B C lets A derive a span when it splits into a left part derived
  by B and a right part derived by C:

      rule-applies? left-has-B? right-has-C? = left-has-B? AND right-has-C?

  over booleans. Proved native and axiom-free: the rule-application test as the
  boolean conjunction of the two subspan memberships (via logic/if-data over Bool);
  that a rule applies when both parts are derivable; that it does NOT apply when the
  left part lacks B; and that it does not apply when the right part lacks C. The
  span iteration and cell union over all split points and rules are executable; what
  is proved is the per-split rule-application decision (a full parse accepts when the
  start symbol reaches the whole-string cell).

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.cyk`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- rule-applies? [left-has-B? right-has-C?]
  (function/app (function/const* 'cyk/rule-applies? []) left-has-B? right-has-C?))

;; Definitions --------------------------------------------------------------

;; rule-applies? left right = if left then right else false   (AND)
(def rule-applies-spec
  {:name 'cyk/rule-applies? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['left-has-B? bool] ['right-has-C? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'left-has-B?) 'left-has-B?
                         'right-has-C? false-value))})

(def definition-specs [rule-applies-spec])

;; Theorems -----------------------------------------------------------------

;; Rule A -> B C applies when the left span derives B and the right span derives C.
(def rule-applies-both-derivable-spec
  {:name 'cyk/rule-applies-both-derivable :universes []
   :type (equality bool (rule-applies? true-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (rule-applies? true-value true-value))})

;; The rule does NOT apply when the left span cannot derive B.
(def rule-fails-left-missing-spec
  {:name 'cyk/rule-fails-left-missing :universes []
   :type (equality bool (rule-applies? false-value true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (rule-applies? false-value true-value))})

;; The rule does NOT apply when the right span cannot derive C.
(def rule-fails-right-missing-spec
  {:name 'cyk/rule-fails-right-missing :universes []
   :type (equality bool (rule-applies? true-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (rule-applies? true-value false-value))})

(def theorem-specs
  [rule-applies-both-derivable-spec rule-fails-left-missing-spec
   rule-fails-right-missing-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-cyk
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
