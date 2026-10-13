(ns rainbow.algorithms.proofs.ahof.o72-branch-and-bound
  "AHoF O72 Branch and Bound (optimization form) worked pruning step over exact
  rationals, reusing the shared bounding lemma (rainbow.algorithms.proofs.branch-and-bound). The
  optimization B&B shares D34's bounding structure: a subtree is pruned when its
  optimistic bound cannot beat the incumbent. Worked instance distinct from D34: a
  node with bound 5 against incumbent 12 is dominated -> pruned (and 5 <= 12 as a
  native at-most, so pruning is sound); a node with bound 15 > incumbent 12 is not
  dominated -> explored. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.o72-branch-and-bound`
  prints this classification."
  (:require [rainbow.algorithms.proofs.branch-and-bound :as dep-branch-and-bound]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- dominated? [bound incumbent]
  (function/app (function/const* 'branch-and-bound/dominated? []) bound incumbent))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Theorems -----------------------------------------------------------------

(def prunes-weak-node-spec
  {:name 'ahof-o72/prunes-weak-node :universes []
   :type (equality bool (dominated? (whole 5) (whole 12)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (dominated? (whole 5) (whole 12)))})

(def pruning-sound-spec
  {:name 'ahof-o72/pruning-sound :universes []
   :type (nnrat-at-most (whole 5) (whole 12))
   :value (at-most-proof (whole 5) (whole 12))})

(def explores-strong-node-spec
  {:name 'ahof-o72/explores-strong-node :universes []
   :type (equality bool (dominated? (whole 15) (whole 12)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (dominated? (whole 15) (whole 12)))})

(def branch-and-bound-spec
  (let [prune-law (:type prunes-weak-node-spec)
        explore-law (:type explores-strong-node-spec)]
    {:name 'ahof-o72/branch-and-bound :universes []
     :type (proposition/conjunction prune-law explore-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      prune-law explore-law
      (function/const* 'ahof-o72/prunes-weak-node [])
      (function/const* 'ahof-o72/explores-strong-node []))}))

(def definition-specs [])
(def theorem-specs
  [prunes-weak-node-spec pruning-sound-spec explores-strong-node-spec
   branch-and-bound-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF O72 branch-and-bound expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native
                               :producer :ahof-o72-branch-and-bound}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF O72 branch-and-bound declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec (dep-branch-and-bound/extend-environment checked-environment)
          (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
