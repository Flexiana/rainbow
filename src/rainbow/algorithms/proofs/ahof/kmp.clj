(ns rainbow.algorithms.proofs.ahof.kmp
  "AHoF Knuth-Morris-Pratt (KMP) string matching: find all occurrences of a
  pattern in a text in O(n + m) time -- never re-examining a text character -- by
  precomputing a FAILURE FUNCTION that says, on a mismatch after matching q
  characters, how far the pattern can shift without missing a match (reusing the
  longest proper prefix that is also a suffix). A full occurrence is reported
  exactly when the running matched-length reaches the pattern length:

      matched? matched-length pattern-length = decide (pattern-length <= matched-length)

  over exact-rational (integer) lengths. Proved native and axiom-free, as worked
  instances: matched length 4 against pattern length 4 reports an occurrence; the
  worked certificate 4 <= 4 (native nnrat/at-most); and a partial match of 2 of 4
  is not yet an occurrence. KMP's correctness and its O(n + m) bound are classical
  and not proved here; the failure function and the scan over the text are
  executable.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.kmp`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- matched? [matched-length pattern-length]
  (function/app (function/const* 'kmp/matched? []) matched-length pattern-length))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; matched? matched-length pattern-length = decide (pattern-length <= matched-length)
(def matched-spec
  {:name 'kmp/matched? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['matched-length nnrat] ['pattern-length nnrat]]
                        (decide-at-most 'pattern-length 'matched-length))})

(def definition-specs [matched-spec])

;; Theorems -----------------------------------------------------------------

;; A matched length 4 reaching the pattern length 4 reports an occurrence.
(def full-match-reports-spec
  {:name 'kmp/full-match-reports :universes []
   :type (equality bool (matched? (whole 4) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (matched? (whole 4) (whole 4)))})

;; Worked certificate for the occurrence above: 4 <= 4.
(def occurrence-matched-whole-pattern-spec
  {:name 'kmp/occurrence-matched-whole-pattern :universes []
   :type (nnrat-at-most (whole 4) (whole 4))
   :value (at-most-proof (whole 4) (whole 4))})

;; A partial match (2 of 4 characters) is not yet an occurrence.
(def partial-match-not-occurrence-spec
  {:name 'kmp/partial-match-not-occurrence :universes []
   :type (equality bool (matched? (whole 2) (whole 4))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (matched? (whole 2) (whole 4)))})

(def theorem-specs
  [full-match-reports-spec occurrence-matched-whole-pattern-spec
   partial-match-not-occurrence-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-kmp
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
