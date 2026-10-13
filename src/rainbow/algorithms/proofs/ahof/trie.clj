(ns rainbow.algorithms.proofs.ahof.trie
  "AHoF Trie (prefix tree): store a set of strings in a tree keyed by characters, so
  that insertion and lookup are O(length) regardless of how many words are stored,
  and every shared prefix is stored once -- the workhorse behind autocomplete,
  spell-check, IP routing, and dictionary compression. A query string is a stored
  WORD exactly when walking its characters reaches an existing node AND that node is
  marked terminal (end-of-word); a prefix query only needs the path to exist:

      is-word? path-complete? terminal? = path-complete? AND terminal?

  over booleans. Proved native and axiom-free: word membership as the boolean
  conjunction of a complete path and a terminal marker (via logic/if-data over
  Bool); that a complete path ending at a terminal node is a stored word; that a
  complete path at a NON-terminal node is only a prefix, not a word; and that an
  incomplete path is neither. The child-map navigation and insertion are executable;
  what is proved is the word-vs-prefix membership decision.

  Requires data/Bool, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.trie`
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

(defn- is-word? [path-complete? terminal?]
  (function/app (function/const* 'trie/is-word? []) path-complete? terminal?))

;; Definitions --------------------------------------------------------------

;; is-word? path-complete? terminal? = if path-complete? then terminal? else false
(def is-word-spec
  {:name 'trie/is-word? :kind :definition :universes []
   :type (function/arrow bool bool bool)
   :value (function/lam
           [['path-complete? bool] ['terminal? bool]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition 'path-complete?) 'path-complete?
                         'terminal? false-value))})

(def definition-specs [is-word-spec])

;; Theorems -----------------------------------------------------------------

;; A complete path ending at a terminal node is a stored word.
(def complete-terminal-is-word-spec
  {:name 'trie/complete-terminal-is-word :universes []
   :type (equality bool (is-word? true-value true-value) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-word? true-value true-value))})

;; A complete path at a non-terminal node is only a prefix, not a stored word.
(def prefix-not-word-spec
  {:name 'trie/prefix-not-word :universes []
   :type (equality bool (is-word? true-value false-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-word? true-value false-value))})

;; An incomplete path (the string is not even a prefix) is not a word.
(def incomplete-path-not-word-spec
  {:name 'trie/incomplete-path-not-word :universes []
   :type (equality bool (is-word? false-value true-value) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (is-word? false-value true-value))})

(def theorem-specs
  [complete-terminal-is-word-spec prefix-not-word-spec
   incomplete-path-not-word-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-trie
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
