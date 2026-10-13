(ns rainbow.algorithms.proofs.interval-membership
  "Interval membership over exact rationals (AHoF V40, decision layer). A value x
  lies in the closed interval [lo, hi] exactly when lo <= x AND x <= hi:

      interval-contains? lo hi x = if (decide lo<=x) then (decide x<=hi) else false

  (boolean AND via logic/if-data over Bool). The endpoint operation for interval
  addition [a,b]+[c,d] = [a+c, b+d] is exact-rational addition of the corresponding
  endpoints:

      interval-add-endpoint p q = p + q.

  This is the membership/decision companion to `rainbow.algorithms.proofs.interval-arithmetic`
  (which proves the interval constructor and the additive enclosure over signed
  rationals); here membership composes the exact-rational order decision with the
  boolean AND, and endpoint addition composes exact-rational addition -- the two
  reusable pieces the worked V40 milestone instance specializes, each with an unfold
  theorem. Proved native and axiom-free.

  Requires audit/decide-nnrat-at-most, logic/if-data, nnrat/add (all present in the
  D63 checkpoint).

  Scope (measured by the kernel): this module has 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.interval-membership`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
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
(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; boolean AND: if a then b else false
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))

(defn- interval-contains? [lo hi x]
  (function/app (function/const* 'validation/interval-contains? []) lo hi x))
(defn- interval-add-endpoint [p q]
  (function/app (function/const* 'validation/interval-add-endpoint []) p q))

;; Definitions --------------------------------------------------------------

;; interval-contains? lo hi x = (lo <= x) AND (x <= hi)
(def interval-contains-spec
  {:name 'validation/interval-contains? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat bool)
   :value (function/lam [['lo nnrat] ['hi nnrat] ['x nnrat]]
                        (and-bool (decide-at-most 'lo 'x)
                                  (decide-at-most 'x 'hi)))})

;; interval-add-endpoint p q = p + q  (endpoint of [a,b]+[c,d] = [a+c, b+d])
(def interval-add-endpoint-spec
  {:name 'validation/interval-add-endpoint :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p nnrat] ['q nnrat]] (nnrat-add 'p 'q))})

(def definition-specs [interval-contains-spec interval-add-endpoint-spec])

;; Theorems -----------------------------------------------------------------

(def interval-contains-unfold-spec
  {:name 'validation/interval-contains-unfold :universes []
   :type (function/forall [['lo nnrat] ['hi nnrat] ['x nnrat]]
                          (equality bool
                                    (interval-contains? 'lo 'hi 'x)
                                    (and-bool (decide-at-most 'lo 'x)
                                              (decide-at-most 'x 'hi))))
   :value (function/lam [['lo nnrat] ['hi nnrat] ['x nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         bool (interval-contains? 'lo 'hi 'x)))})

(def interval-add-endpoint-unfold-spec
  {:name 'validation/interval-add-endpoint-unfold :universes []
   :type (function/forall [['p nnrat] ['q nnrat]]
                          (equality nnrat
                                    (interval-add-endpoint 'p 'q)
                                    (nnrat-add 'p 'q)))
   :value (function/lam [['p nnrat] ['q nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (interval-add-endpoint 'p 'q)))})

(def theorem-specs
  [interval-contains-unfold-spec interval-add-endpoint-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Interval-membership expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :interval-membership}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Interval-membership declaration rejected"
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
