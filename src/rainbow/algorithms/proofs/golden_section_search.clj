(ns rainbow.algorithms.proofs.golden-section-search
  "Golden Section Search interval reduction over exact rationals (AHoF O9). A
  unimodal minimum is bracketed in [a, b]; two interior probe points c < d are
  evaluated, and the sub-interval on the side of the SMALLER interior value is kept,
  shrinking the bracket each iteration. The reduction decision compares the two
  interior values, and the retained interior value is their minimum:

      keep-left?   fc fd = decide (fc <= fd)       (keep [a, d] when fc <= fd)
      retained-min fc fd = if (fc <= fd) then fc else fd   (min via if-data / nnrat)

  over exact rationals. Golden Section and Fibonacci Search share this skeleton; only
  the probe-point placement differs. Proved native and axiom-free: the reduction
  decision and the retained-minimum selection, each with an unfold theorem.

  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.golden-section-search`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; if (fc <= fd) then fc else fd  -- the minimum, via the Bool eliminator over nnrat
(defn- select-min-body [fc fd]
  (let [decision (decide-at-most fc fd)]
    (function/app (function/const* 'logic/if-data [type-level])
                  nnrat (condition decision) decision fc fd)))

(defn- keep-left? [fc fd]
  (function/app (function/const* 'linesearch/keep-left? []) fc fd))
(defn- retained-min [fc fd]
  (function/app (function/const* 'linesearch/retained-min []) fc fd))

;; Definitions --------------------------------------------------------------

;; keep-left? fc fd = decide (fc <= fd)
(def keep-left-spec
  {:name 'linesearch/keep-left? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['fc nnrat] ['fd nnrat]] (decide-at-most 'fc 'fd))})

;; retained-min fc fd = if (fc <= fd) then fc else fd
(def retained-min-spec
  {:name 'linesearch/retained-min :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['fc nnrat] ['fd nnrat]] (select-min-body 'fc 'fd))})

(def definition-specs [keep-left-spec retained-min-spec])

;; Theorems -----------------------------------------------------------------

(def keep-left-unfold-spec
  {:name 'linesearch/keep-left-unfold :universes []
   :type (function/forall [['fc nnrat] ['fd nnrat]]
                          (equality bool (keep-left? 'fc 'fd)
                                    (decide-at-most 'fc 'fd)))
   :value (function/lam [['fc nnrat] ['fd nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (keep-left? 'fc 'fd)))})

(def retained-min-unfold-spec
  {:name 'linesearch/retained-min-unfold :universes []
   :type (function/forall [['fc nnrat] ['fd nnrat]]
                          (equality nnrat (retained-min 'fc 'fd)
                                    (select-min-body 'fc 'fd)))
   :value (function/lam [['fc nnrat] ['fd nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (retained-min 'fc 'fd)))})

(def theorem-specs [keep-left-unfold-spec retained-min-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Golden-section expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :golden-section-search}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Golden-section declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.golden-section-search))
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
