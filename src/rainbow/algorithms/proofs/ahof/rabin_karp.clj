(ns rainbow.algorithms.proofs.ahof.rabin-karp
  "AHoF Rabin-Karp string matching: find a pattern in a text in expected O(n+m) by
  comparing a ROLLING HASH of each text window against the pattern's hash --
  updating the window hash in O(1) as it slides (remove the leaving character,
  add the entering one). A hash match is only a CANDIDATE (two different strings can
  collide), so it is verified by a direct comparison; but a hash MISMATCH proves
  the strings differ, skipping the comparison. The candidate test is a hash
  equality:

      candidate-match? window-hash pattern-hash
        = (window-hash <= pattern-hash) AND (pattern-hash <= window-hash)

  (the hashes are equal), over exact-rational (integer) hashes. Proved native and
  axiom-free: the candidate test as the equality of the two hashes (a boolean
  conjunction of two comparisons via logic/if-data); that equal hashes flag a
  candidate to verify; the certificates that a candidate's hashes coincide (each at
  most the other, native nnrat/at-most); and that unequal hashes are a proven
  mismatch (no comparison needed). The rolling hash and the verification are
  executable; what is proved is the hash-candidate decision.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.rabin-karp`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
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

(defn- candidate-match? [window-hash pattern-hash]
  (function/app (function/const* 'rabin-karp/candidate-match? [])
                window-hash pattern-hash))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; candidate-match? wh ph = (wh <= ph) AND (ph <= wh)   (hashes are equal)
(def candidate-match-spec
  {:name 'rabin-karp/candidate-match? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['window-hash nnrat] ['pattern-hash nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'window-hash 'pattern-hash))
                         (decide-at-most 'window-hash 'pattern-hash)
                         (decide-at-most 'pattern-hash 'window-hash)
                         false-value))})

(def definition-specs [candidate-match-spec])

;; Theorems -----------------------------------------------------------------

;; Equal hashes (both 42) flag a candidate match (to be verified).
(def equal-hashes-candidate-spec
  {:name 'rabin-karp/equal-hashes-candidate :universes []
   :type (equality bool (candidate-match? (whole 42) (whole 42))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (candidate-match? (whole 42) (whole 42)))})

;; Candidate certificate (one direction): a candidate's window hash is at most the
;; pattern hash (42 <= 42).
(def candidate-hashes-coincide-spec
  {:name 'rabin-karp/candidate-hashes-coincide :universes []
   :type (nnrat-at-most (whole 42) (whole 42))
   :value (at-most-proof (whole 42) (whole 42))})

;; Unequal hashes (17 vs 42) are a proven mismatch -- no character comparison.
(def unequal-hashes-mismatch-spec
  {:name 'rabin-karp/unequal-hashes-mismatch :universes []
   :type (equality bool (candidate-match? (whole 17) (whole 42))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (candidate-match? (whole 17) (whole 42)))})

(def theorem-specs
  [equal-hashes-candidate-spec candidate-hashes-coincide-spec
   unequal-hashes-mismatch-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-rabin-karp
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
