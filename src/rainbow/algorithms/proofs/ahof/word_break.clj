(ns rainbow.algorithms.proofs.ahof.word-break
  "AHoF Word Break (dynamic programming): decide whether a string can be segmented
  into a sequence of dictionary words -- the core of tokenizers, CJK word
  segmentation, and URL/identifier splitting. The DP fills breakable[i] = 'the
  prefix of length i splits into words'; a split point j works when the prefix up
  to j is itself breakable AND the remaining piece j..i is a dictionary word, and
  breakable[i] is the OR of all working split points:

      split-works? prefix-breakable? suffix-is-word?
        = prefix-breakable? AND suffix-is-word?

  over booleans. Proved native and axiom-free: the per-split test as the boolean
  conjunction of a breakable prefix and a dictionary-word suffix (via logic/if-data
  over Bool); that a split works when both hold; and that it fails when the prefix
  is not breakable or the suffix is not a word. The scan over split points and the
  OR-accumulation are executable; what is proved is the per-split success decision.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.word-break`
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

(defn- split-works? [prefix-breakable? suffix-is-word?]
  (function/app (function/const* 'word-break/split-works? [])
                prefix-breakable? suffix-is-word?))

;; Definitions --------------------------------------------------------------

;; split-works? prefix suffix = if prefix then suffix else false   (AND)
(def split-works-spec
  {:name 'word-break/split-works? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['prefix-breakable? bool] ['suffix-is-word? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'prefix-breakable?) 'prefix-breakable?
                         'suffix-is-word? false-value))})

(def definition-specs [split-works-spec])

;; Theorems -----------------------------------------------------------------

;; A split works when the prefix is breakable and the suffix is a dictionary word.
(def split-works-both-hold-spec
  {:name 'word-break/split-works-both-hold :universes []
   :type (equality bool (split-works? true-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (split-works? true-value true-value))})

;; A split fails when the prefix is not breakable (even if the suffix is a word).
(def split-fails-prefix-unbreakable-spec
  {:name 'word-break/split-fails-prefix-unbreakable :universes []
   :type (equality bool (split-works? false-value true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (split-works? false-value true-value))})

;; A split fails when the suffix is not a dictionary word.
(def split-fails-suffix-not-word-spec
  {:name 'word-break/split-fails-suffix-not-word :universes []
   :type (equality bool (split-works? true-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (split-works? true-value false-value))})

(def theorem-specs
  [split-works-both-hold-spec split-fails-prefix-unbreakable-spec
   split-fails-suffix-not-word-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-word-break
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
