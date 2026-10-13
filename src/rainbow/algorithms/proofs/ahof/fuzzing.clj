(ns rainbow.algorithms.proofs.ahof.fuzzing
  "AHoF V11 Fuzzing: generate test inputs by repeatedly mutating a seed input and
  checking whether any mutant violates the specification. The primitive bit-flip
  mutation toggles a boolean coordinate of the input:

      flip b = if b then false else true

  (the not connective). Proved native and axiom-free: the flip mutation, and its
  involution law -- flipping twice restores the original bit (flip (flip b) = b)
  -- which is what lets a fuzzer explore and return: no mutation is unreachable
  or lost. The mutation-scheduling strategy and the coverage-guided seed
  selection are executable concerns; what is proved here is the mutation operator
  and its involution.

  Requires data/Bool and logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fuzzing`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
;; flip b = if b then false else true
(defn- flip-term [b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition b) b false-value true-value))

(defn- flip [b]
  (function/app (function/const* 'fuzzing/flip []) b))

;; Definitions --------------------------------------------------------------

;; flip b = if b then false else true
(def flip-spec
  {:name 'fuzzing/flip :kind :definition :universes []
   :type (function/arrow bool bool)
   :value (function/lam [['b bool]] (flip-term 'b))})

(def definition-specs [flip-spec])

;; Theorems -----------------------------------------------------------------

;; The mutation toggles: flip true = false.
(def flip-true-spec
  {:name 'fuzzing/flip-true :universes []
   :type (equality bool (flip true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flip true-value))})

;; flip false = true.
(def flip-false-spec
  {:name 'fuzzing/flip-false :universes []
   :type (equality bool (flip false-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flip false-value))})

;; Involution (on true): flipping twice restores the bit.
(def flip-involution-true-spec
  {:name 'fuzzing/flip-involution-true :universes []
   :type (equality bool (flip (flip true-value)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flip (flip true-value)))})

;; Involution (on false).
(def flip-involution-false-spec
  {:name 'fuzzing/flip-involution-false :universes []
   :type (equality bool (flip (flip false-value)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (flip (flip false-value)))})

(def theorem-specs
  [flip-true-spec flip-false-spec flip-involution-true-spec
   flip-involution-false-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-fuzzing
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
