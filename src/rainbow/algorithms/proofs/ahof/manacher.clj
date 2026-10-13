(ns rainbow.algorithms.proofs.ahof.manacher
  "AHoF Manacher's Algorithm: find the longest palindromic substring (and all
  maximal palindrome radii) in LINEAR time, beating the O(n^2) expand-around-center
  approach by reusing mirror symmetry so each position is examined O(1) amortized.
  The one primitive operation, whether an expand-around-center step continues, is a
  character MATCH between the mirrored positions:

      characters-match? left-char right-char
        = (left-char <= right-char) AND (right-char <= left-char)

  (the two characters are equal), over exact-rational (integer) character codes.
  The match test is defined as a conjunction of two comparisons via logic/if-data.
  Proved native and axiom-free, as worked instances: codes 65 and 65 match; the
  one-direction worked certificate 65 <= 65 (native nnrat/at-most); and codes 65
  and 66 do not match. Manacher's correctness and its linear-time bound are
  classical and not proved here; the center iteration with mirror-radius reuse is
  executable.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.manacher`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- condition [decision] (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

(defn- characters-match? [left-char right-char]
  (function/app (function/const* 'manacher/characters-match? [])
                left-char right-char))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; characters-match? l r = (l <= r) AND (r <= l)   (characters are equal)
(def characters-match-spec
  {:name 'manacher/characters-match? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['left-char nnrat] ['right-char nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'left-char 'right-char))
                         (decide-at-most 'left-char 'right-char)
                         (decide-at-most 'right-char 'left-char)
                         false-value))})

(def definition-specs [characters-match-spec])

;; Theorems -----------------------------------------------------------------

;; Mirrored characters with the same code (both 65 = 'A') match: the palindrome
;; extends.
(def equal-chars-extend-spec
  {:name 'manacher/equal-chars-extend :universes []
   :type (equality bool (characters-match? (whole 65) (whole 65))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (characters-match? (whole 65) (whole 65)))})

;; Worked certificate (one direction) for the match above: 65 <= 65.
(def matching-chars-coincide-spec
  {:name 'manacher/matching-chars-coincide :universes []
   :type (nnrat-at-most (whole 65) (whole 65))
   :value (at-most-proof (whole 65) (whole 65))})

;; Different characters (65 = 'A' vs 66 = 'B') stop the expansion.
(def different-chars-stop-spec
  {:name 'manacher/different-chars-stop :universes []
   :type (equality bool (characters-match? (whole 65) (whole 66))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (characters-match? (whole 65) (whole 66)))})

(def theorem-specs
  [equal-chars-extend-spec matching-chars-coincide-spec different-chars-stop-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-manacher (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.manacher))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
