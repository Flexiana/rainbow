(ns rainbow.algorithms.proofs.ahof.fibonacci-search
  "AHoF O8 worked Fibonacci Search reduction step over exact rationals, reusing the
  shared bracket-reduction lemma (rainbow.algorithms.proofs.golden-section-search, linesearch/*).
  Fibonacci and Golden Section Search share the same ITERATE loop and differ only in
  probe-point placement; here the Fibonacci probes evaluate to 3/8 (left) and 5/8
  (right). Since the left value 3/8 is at most the right value 5/8, the left
  sub-interval is kept and the retained interior value is 3/8; swapping the probes
  keeps the right sub-interval and still retains 3/8. This second catalog row is
  discharged entirely by the reused general lemma -- a demonstration of lemma
  leverage. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 5 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.fibonacci-search`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.algorithms.proofs.golden-section-search :as dep-golden-section-search]
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

(def three-eighths (make-rational (data-nat 3) (data-nat 7)))  ; 3/8
(def five-eighths (make-rational (data-nat 5) (data-nat 7)))   ; 5/8

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- keep-left? [fc fd]
  (function/app (function/const* 'linesearch/keep-left? []) fc fd))
(defn- retained-min [fc fd]
  (function/app (function/const* 'linesearch/retained-min []) fc fd))

;; Definitions --------------------------------------------------------------

(def left-value-spec
  {:name 'ahof-o8/left-value :kind :definition :universes [] :type nnrat
   :value three-eighths})
(def right-value-spec
  {:name 'ahof-o8/right-value :kind :definition :universes [] :type nnrat
   :value five-eighths})

(def fc (function/const* 'ahof-o8/left-value []))
(def fd (function/const* 'ahof-o8/right-value []))

(def definition-specs [left-value-spec right-value-spec])

;; Theorems -----------------------------------------------------------------

(def keeps-left-spec
  {:name 'ahof-o8/keeps-left :universes []
   :type (equality bool (keep-left? fc fd) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-left? fc fd))})

(def retains-min-left-spec
  {:name 'ahof-o8/retains-min-left :universes []
   :type (equality nnrat (retained-min fc fd) three-eighths)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (retained-min fc fd))})

(def keeps-right-when-swapped-spec
  {:name 'ahof-o8/keeps-right-when-swapped :universes []
   :type (equality bool (keep-left? fd fc) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (keep-left? fd fc))})

(def retains-min-right-spec
  {:name 'ahof-o8/retains-min-right :universes []
   :type (equality nnrat (retained-min fd fc) three-eighths)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (retained-min fd fc))})

(def fibonacci-search-spec
  (let [keep-law (:type keeps-left-spec)
        min-law (:type retains-min-left-spec)]
    {:name 'ahof-o8/fibonacci-search :universes []
     :type (proposition/conjunction keep-law min-law)
     :value
     (function/app
      (function/const* 'proposition/conjoin [])
      keep-law min-law
      (function/const* 'ahof-o8/keeps-left [])
      (function/const* 'ahof-o8/retains-min-left []))}))

(def theorem-specs
  [keeps-left-spec retains-min-left-spec keeps-right-when-swapped-spec
   retains-min-right-spec fibonacci-search-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF fibonacci-search expression failed elaboration"
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
                               :producer :ahof-o8-fibonacci-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "AHoF fibonacci-search declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.golden-section-search])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.fibonacci-search))
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
