(ns rainbow.algorithms.proofs.bisection
  "Bisection bracket search over exact nonnegative rationals. The probe point of a
  bracket [lo, hi] is its midpoint (lo + hi) / 2; narrowing keeps the lower or
  upper half depending on a pluggable test, exactly halving the interval. All
  bracket methods share this ITERATE loop and differ only in the probe point
  (AHoF O12, the simplest instance).

  Scope (measured by the kernel): this module has 3 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.bisection`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def bool-false (function/const* 'data/false []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-half (function/const* 'nnrat/half []))
(def bracket (function/app (function/const* 'data/Product [type-level type-level])
                           nnrat nnrat))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- pair [lo hi]
  (function/app (function/const* 'data/pair [type-level type-level])
                nnrat nnrat lo hi))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- midpoint [lo hi]
  (function/app (function/const* 'search/bracket-midpoint []) lo hi))

;; A self-contained documentation proposition for the if-data condition slot.
(defn- condition [keep-lower]
  (function/equality type-level bool keep-lower keep-lower))

(defn- if-bracket [decision then-value else-value]
  (function/app (function/const* 'logic/if-data [type-level])
                bracket (condition decision) decision then-value else-value))

;; Definitions --------------------------------------------------------------

(def midpoint-spec
  {:name 'search/bracket-midpoint :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam
           [['lo nnrat] ['hi nnrat]]
           (nnrat-multiply (nnrat-add 'lo 'hi) nnrat-half))})

(def narrow-spec
  {:name 'search/bisection-narrow :kind :definition :universes []
   :type (function/arrow bool nnrat nnrat bracket)
   :value (function/lam
           [['keep-lower bool] ['lo nnrat] ['hi nnrat]]
           (if-bracket 'keep-lower
                       (pair 'lo (midpoint 'lo 'hi))
                       (pair (midpoint 'lo 'hi) 'hi)))})

(def definition-specs [midpoint-spec narrow-spec])

;; Theorems -----------------------------------------------------------------

(defn- narrow [keep-lower lo hi]
  (function/app (function/const* 'search/bisection-narrow [])
                keep-lower lo hi))

(def midpoint-unfold-spec
  {:name 'search/bracket-midpoint-unfold :universes []
   :type (function/forall
          [['lo nnrat] ['hi nnrat]]
          (equality nnrat (midpoint 'lo 'hi)
                    (nnrat-multiply (nnrat-add 'lo 'hi) nnrat-half)))
   :value (function/lam
           [['lo nnrat] ['hi nnrat]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         nnrat (midpoint 'lo 'hi)))})

;; When the test keeps the lower half, the bracket becomes [lo, midpoint].
(def narrow-lower-spec
  (let [true-const (function/const* 'data/true [])]
    {:name 'search/narrow-keeps-lower :universes []
     :type (function/forall
            [['lo nnrat] ['hi nnrat]
             ['keep (equality bool true-const true-const)]]
            (equality bracket
                      (narrow true-const 'lo 'hi)
                      (pair 'lo (midpoint 'lo 'hi))))
     :value (function/lam
             [['lo nnrat] ['hi nnrat]
              ['keep (equality bool true-const true-const)]]
             (function/app (function/const* 'equality/reflexive [type-level])
                           bracket (pair 'lo (midpoint 'lo 'hi))))}))

;; When the test keeps the upper half, the bracket becomes [midpoint, hi].
(def narrow-upper-spec
  {:name 'search/narrow-keeps-upper :universes []
   :type (function/forall
          [['lo nnrat] ['hi nnrat]
           ['reject (equality bool (function/const* 'data/false [])
                              bool-false)]]
          (equality bracket
                    (narrow bool-false 'lo 'hi)
                    (pair (midpoint 'lo 'hi) 'hi)))
   :value (function/lam
           [['lo nnrat] ['hi nnrat]
            ['reject (equality bool (function/const* 'data/false [])
                               bool-false)]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         bracket (pair (midpoint 'lo 'hi) 'hi)))})

(def theorem-specs
  [midpoint-unfold-spec narrow-lower-spec narrow-upper-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Bisection expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :bisection}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Bisection declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
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
