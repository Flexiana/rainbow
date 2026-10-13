(ns rainbow.algorithms.proofs.ahof.bloom-filter
  "AHoF Bloom Filter: a space-efficient probabilistic set that answers membership
  with NO FALSE NEGATIVES (if it says absent, the element was never added) but
  possible false positives. An element sets k hash-indexed bits on insertion; a
  query returns 'possibly present' only when ALL k of its bits are set:

      possibly-present? bit-a bit-b = bit-a AND bit-b

  (shown for k = 2 hash bits), over booleans. Defined: the membership test as a
  boolean conjunction of the queried bits (via logic/if-data over Bool). Proved
  native and axiom-free, as worked instances: bits (true, true) give possibly
  present, and bits (false, true) and (true, false) each give absent. The
  structure's classical no-false-negatives guarantee is not proved here. The hash
  functions and the bit array are executable.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.bloom-filter`
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

(defn- possibly-present? [bit-a bit-b]
  (function/app (function/const* 'bloom-filter/possibly-present? []) bit-a bit-b))

;; Definitions --------------------------------------------------------------

;; possibly-present? bit-a bit-b = if bit-a then bit-b else false  (AND)
(def possibly-present-spec
  {:name 'bloom-filter/possibly-present? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['bit-a bool] ['bit-b bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'bit-a) 'bit-a 'bit-b false-value))})

(def definition-specs [possibly-present-spec])

;; Theorems -----------------------------------------------------------------

;; An element whose bits are all set (true, true) is possibly present.
(def all-bits-set-possibly-present-spec
  {:name 'bloom-filter/all-bits-set-possibly-present :universes []
   :type (equality bool (possibly-present? true-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (possibly-present? true-value true-value))})

;; Worked instance: bits (false, true) give absent. The classical
;; no-false-negatives guarantee is not proved here.
(def unset-first-bit-absent-spec
  {:name 'bloom-filter/unset-first-bit-absent :universes []
   :type (equality bool (possibly-present? false-value true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (possibly-present? false-value true-value))})

;; Worked instance: bits (true, false) give absent.
(def unset-second-bit-absent-spec
  {:name 'bloom-filter/unset-second-bit-absent :universes []
   :type (equality bool (possibly-present? true-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (possibly-present? true-value false-value))})

(def theorem-specs
  [all-bits-set-possibly-present-spec unset-first-bit-absent-spec
   unset-second-bit-absent-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-bloom-filter
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
