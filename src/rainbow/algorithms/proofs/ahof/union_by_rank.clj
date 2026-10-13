(ns rainbow.algorithms.proofs.ahof.union-by-rank
  "AHoF Union by Rank: the balancing optimization that keeps a Union-Find (disjoint
  set) forest shallow, so find/union run in near-constant amortized time (inverse
  Ackermann, with path compression). When merging two sets, the root of the
  SHALLOWER tree is attached under the root of the deeper one -- comparing ranks
  (upper bounds on tree height) decides which becomes the child:

      attach-under? rank-a rank-b = decide (rank-a <= rank-b)

  (attach root A under root B when A's rank is at most B's), over exact-rational
  (integer) ranks. Proved native and axiom-free: the attach decision; that the
  lower-rank root is attached under the higher-rank root; the certificate that the
  attached root really has rank at most the other's (native nnrat/at-most) -- so the
  merged tree's height does not grow unnecessarily; and that a higher-rank root
  becomes the parent. The parent pointers and path compression are executable; what
  is proved is the union-by-rank attach decision.

  Requires nnrat/at-most, audit/decide-nnrat-at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.union-by-rank`
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

(defn- attach-under? [rank-a rank-b]
  (function/app (function/const* 'union-by-rank/attach-under? []) rank-a rank-b))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; attach-under? rank-a rank-b = decide (rank-a <= rank-b)
(def attach-under-spec
  {:name 'union-by-rank/attach-under? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['rank-a nnrat] ['rank-b nnrat]]
                        (decide-at-most 'rank-a 'rank-b))})

(def definition-specs [attach-under-spec])

;; Theorems -----------------------------------------------------------------

;; Root A (rank 2) is attached under root B (rank 4) -- the shallower under the
;; deeper.
(def lower-rank-attached-under-spec
  {:name 'union-by-rank/lower-rank-attached-under :universes []
   :type (equality bool (attach-under? (whole 2) (whole 4))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (attach-under? (whole 2) (whole 4)))})

;; Certificate: the attached root's rank is at most the other's (2 <= 4), so the
;; merged tree's height does not grow unnecessarily.
(def attached-rank-at-most-spec
  {:name 'union-by-rank/attached-rank-at-most :universes []
   :type (nnrat-at-most (whole 2) (whole 4))
   :value (at-most-proof (whole 2) (whole 4))})

;; A higher-rank root (5) is not attached under a lower-rank one (3) -- it becomes
;; the parent instead.
(def higher-rank-becomes-parent-spec
  {:name 'union-by-rank/higher-rank-becomes-parent :universes []
   :type (equality bool (attach-under? (whole 5) (whole 3))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (attach-under? (whole 5) (whole 3)))})

(def theorem-specs
  [lower-rank-attached-under-spec attached-rank-at-most-spec
   higher-rank-becomes-parent-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-union-by-rank
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
