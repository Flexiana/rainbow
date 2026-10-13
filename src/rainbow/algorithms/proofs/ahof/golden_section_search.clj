(ns rainbow.algorithms.proofs.ahof.golden-section-search
  "AHoF O9 worked Golden Section Search reduction step over exact rationals. Two
  interior probe values are compared. When the left value 1/2 is at most the right
  value 3/4, the left sub-interval is kept and the retained minimum is 1/2. When the
  probe values are swapped (3/4 on the left, 1/2 on the right) the right sub-interval
  is kept and the retained minimum is still 1/2 -- in both orientations of this
  pair the search retains the smaller interior value. Proved native and
  axiom-free.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.golden-section-search`
  prints this classification."
  (:require [rainbow.algorithms.proofs.golden-section-search :as dep-golden-section-search]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [numerator denominator-predecessor]
  (function/app (function/const* 'nnrat/make []) numerator
                denominator-predecessor))

(def half (make-rational (data-nat 1) (data-nat 1)))            ; 1/2
(def three-quarters (make-rational (data-nat 3) (data-nat 3)))  ; 3/4

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- keep-left? [fc fd]
  (function/app (function/const* 'linesearch/keep-left? []) fc fd))
(defn- retained-min [fc fd]
  (function/app (function/const* 'linesearch/retained-min []) fc fd))

;; Definitions --------------------------------------------------------------

(def left-value-spec
  {:name 'ahof-o9/left-value :kind :definition :universes [] :type nnrat
   :value half})
(def right-value-spec
  {:name 'ahof-o9/right-value :kind :definition :universes [] :type nnrat
   :value three-quarters})

(def fc (function/const* 'ahof-o9/left-value []))
(def fd (function/const* 'ahof-o9/right-value []))

(def definition-specs [left-value-spec right-value-spec])

;; Theorems -----------------------------------------------------------------

;; The smaller interior value is on the left, so the left sub-interval is kept.
(def keeps-left-spec
  {:name 'ahof-o9/keeps-left :universes []
   :type (equality bool (keep-left? fc fd) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-left? fc fd))})

;; The retained interior value is the minimum 1/2.
(def retains-min-left-spec
  {:name 'ahof-o9/retains-min-left :universes []
   :type (equality nnrat (retained-min fc fd) half)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (retained-min fc fd))})

;; With the probe values swapped, the right sub-interval is kept instead.
(def keeps-right-when-swapped-spec
  {:name 'ahof-o9/keeps-right-when-swapped :universes []
   :type (equality bool (keep-left? fd fc) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-left? fd fc))})

;; ...and the retained value is still the minimum 1/2.
(def retains-min-right-spec
  {:name 'ahof-o9/retains-min-right :universes []
   :type (equality nnrat (retained-min fd fc) half)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (retained-min fd fc))})

;; The worked O9 package: the left probe is kept and its value is the retained
;; minimum.
(def golden-section-spec
  (let [keep-law (:type keeps-left-spec)
        min-law (:type retains-min-left-spec)]
    {:name 'ahof-o9/golden-section :universes []
     :type (proposition/conjunction keep-law min-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      keep-law min-law
      (function/const* 'ahof-o9/keeps-left [])
      (function/const* 'ahof-o9/retains-min-left []))}))

(def theorem-specs
  [keeps-left-spec retains-min-left-spec keeps-right-when-swapped-spec
   retains-min-right-spec golden-section-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF golden-section expression failed elaboration"
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
                               :producer :ahof-o9-golden-section-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF golden-section declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec (dep-golden-section-search/extend-environment checked-environment)
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
