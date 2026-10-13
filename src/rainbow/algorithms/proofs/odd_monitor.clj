(ns rainbow.algorithms.proofs.odd-monitor
  "Operational Design Domain (ODD) monitoring over exact rationals (AHoF V59). An
  ODD is a multi-dimensional operating envelope -- here a 2-D box
  [lo1,hi1] x [lo2,hi2]. The monitor accepts an operating point (x1, x2) exactly
  when it lies inside the box on BOTH dimensions, i.e. the four-way conjunction

      in-odd? = (lo1<=x1) AND (x1<=hi1) AND (lo2<=x2) AND (x2<=hi2)

  built as nested boolean ANDs (logic/if-data over Bool) of the exact-rational order
  decisions. A single out-of-range coordinate takes the point outside the ODD, which
  is exactly the runtime-monitor alarm condition. Proved native and axiom-free: the
  membership decision as the four-way conjunction, with its unfold theorem.

  Requires audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.odd-monitor`
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
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; boolean AND: if a then b else false
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))

;; membership on one dimension: (lo <= x) AND (x <= hi)
(defn- within-dim [lo hi x]
  (and-bool (decide-at-most lo x) (decide-at-most x hi)))

;; four-way ODD-box membership over both dimensions
(defn- in-odd-body [lo1 hi1 x1 lo2 hi2 x2]
  (and-bool (within-dim lo1 hi1 x1) (within-dim lo2 hi2 x2)))

(defn- in-odd? [lo1 hi1 x1 lo2 hi2 x2]
  (function/app (function/const* 'monitor/in-odd? []) lo1 hi1 x1 lo2 hi2 x2))

;; Definitions --------------------------------------------------------------

(def in-odd-spec
  {:name 'monitor/in-odd? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat bool)
   :value (function/lam [['lo1 nnrat] ['hi1 nnrat] ['x1 nnrat]
                         ['lo2 nnrat] ['hi2 nnrat] ['x2 nnrat]]
                        (in-odd-body 'lo1 'hi1 'x1 'lo2 'hi2 'x2))})

(def definition-specs [in-odd-spec])

;; Theorems -----------------------------------------------------------------

(def in-odd-unfold-spec
  {:name 'monitor/in-odd-unfold :universes []
   :type (function/forall [['lo1 nnrat] ['hi1 nnrat] ['x1 nnrat]
                           ['lo2 nnrat] ['hi2 nnrat] ['x2 nnrat]]
                          (equality bool
                                    (in-odd? 'lo1 'hi1 'x1 'lo2 'hi2 'x2)
                                    (in-odd-body 'lo1 'hi1 'x1 'lo2 'hi2 'x2)))
   :value (function/lam [['lo1 nnrat] ['hi1 nnrat] ['x1 nnrat]
                         ['lo2 nnrat] ['hi2 nnrat] ['x2 nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (in-odd? 'lo1 'hi1 'x1 'lo2 'hi2 'x2)))})

(def theorem-specs [in-odd-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "ODD-monitor expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :odd-monitor}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "ODD-monitor declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.odd-monitor))
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
