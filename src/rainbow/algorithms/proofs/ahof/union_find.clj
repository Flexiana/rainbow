(ns rainbow.algorithms.proofs.ahof.union-find
  "AHoF Union-Find (Disjoint-Set) connectivity: maintain a partition of elements
  into disjoint sets under union operations, answering connectivity queries by
  comparing set representatives. Two elements are connected exactly when they have
  the same representative -- an equality decided by antisymmetry (each is at most
  the other):

      connected? ra rb = (ra <= rb) AND (rb <= ra)

  over the exact-rational representative ids. Proved native and axiom-free: the
  connectivity test as a boolean conjunction of two decidable comparisons; that
  equal representatives are connected; that distinct representatives are not; and
  the certificate that connected elements' representatives coincide (each <= the
  other as native nnrat/at-most, i.e. antisymmetry). The union operation and the
  find-with-path-compression are executable; what is proved is the connectivity
  decision. This is the connectivity primitive behind Kruskal's MST and dynamic
  connectivity.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/at-most,
  nnrat/decide-at-most-true-sound (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.union-find`
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

(defn- connected? [ra rb]
  (function/app (function/const* 'union-find/connected? []) ra rb))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; connected? ra rb = (ra <= rb) AND (rb <= ra)   (representatives are equal)
(def connected-spec
  {:name 'union-find/connected? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam
           [['ra nnrat] ['rb nnrat]]
           (function/app (function/const* 'logic/if-data [type-level])
                         bool (condition (decide-at-most 'ra 'rb))
                         (decide-at-most 'ra 'rb)
                         (decide-at-most 'rb 'ra)
                         false-value))})

(def definition-specs [connected-spec])

;; Theorems -----------------------------------------------------------------

;; Two elements with the same representative (3, 3) are connected.
(def same-representative-connected-spec
  {:name 'union-find/same-representative-connected :universes []
   :type (equality bool (connected? (whole 3) (whole 3))
                   (function/const* 'data/true []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (connected? (whole 3) (whole 3)))})

;; Elements in different sets (representatives 3 and 5) are not connected.
(def different-representative-disconnected-spec
  {:name 'union-find/different-representative-disconnected :universes []
   :type (equality bool (connected? (whole 3) (whole 5))
                   (function/const* 'data/false []))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (connected? (whole 3) (whole 5)))})

;; Certificate (antisymmetry, one direction): connected reps satisfy ra <= rb.
(def connected-implies-le-spec
  {:name 'union-find/connected-implies-le :universes []
   :type (nnrat-at-most (whole 3) (whole 3))
   :value (at-most-proof (whole 3) (whole 3))})

(def theorem-specs
  [same-representative-connected-spec different-representative-disconnected-spec
   connected-implies-le-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-union-find
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
