(ns rainbow.algorithms.proofs.newton
  "Newton's method as the general descent skeleton with a Hessian-inverse step
  size. Where gradient descent uses a fixed rate, Newton scales the step by the
  reciprocal of the second derivative: the step size at a point is
  `1 / hessian(point)`, computed with exact rational division. On a quadratic
  objective this makes Newton reach the minimum in a single step (AHoF O26). Only
  the step-size function is new; the descent loop is the O13 skeleton.

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.newton`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def hessian-type (function/arrow signed nnrat))

(defn- reciprocal [value]
  (function/app (function/const* 'nnrat/reciprocal []) value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- newton-rate [hessian point]
  (function/app (function/const* 'optimization/newton-rate []) hessian point))

;; Definitions --------------------------------------------------------------

;; The Newton step size at a point: the reciprocal of the Hessian there.
(def newton-rate-spec
  {:name 'optimization/newton-rate :kind :definition :universes []
   :type (function/forall [['hessian hessian-type] ['point signed]] nnrat)
   :value (function/lam [['hessian hessian-type] ['point signed]]
                        (reciprocal (function/app 'hessian 'point)))})

(def definition-specs [newton-rate-spec])

;; Theorems -----------------------------------------------------------------

(def newton-rate-unfold-spec
  {:name 'optimization/newton-rate-unfold :universes []
   :type (function/forall
          [['hessian hessian-type] ['point signed]]
          (equality nnrat (newton-rate 'hessian 'point)
                    (reciprocal (function/app 'hessian 'point))))
   :value (function/lam [['hessian hessian-type] ['point signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (newton-rate 'hessian 'point)))})

(def theorem-specs [newton-rate-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Newton expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :newton}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Newton declaration rejected"
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
