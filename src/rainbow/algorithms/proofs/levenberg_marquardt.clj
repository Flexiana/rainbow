(ns rainbow.algorithms.proofs.levenberg-marquardt
  "Levenberg-Marquardt as the general descent skeleton with a damped
  Hessian-inverse step size. The step size at a point is
  `1 / (hessian(point) + lambda)`, interpolating between Newton's method
  (lambda = 0) and small gradient steps (large lambda). The damping parameter
  lambda keeps the step well-defined even when the Hessian is small, using exact
  rational division and addition (AHoF O31). Only the step-size function is new;
  the descent loop is the O13 skeleton.

  Scope (measured by the kernel): this module has 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.levenberg-marquardt`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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
(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- lm-rate [hessian lambda point]
  (function/app (function/const* 'optimization/levenberg-marquardt-rate [])
                hessian lambda point))

;; Definitions --------------------------------------------------------------

;; The damped step size: 1 / (hessian(point) + lambda).
(def lm-rate-spec
  {:name 'optimization/levenberg-marquardt-rate :kind :definition :universes []
   :type (function/forall [['hessian hessian-type] ['lambda nnrat]
                           ['point signed]]
                          nnrat)
   :value (function/lam [['hessian hessian-type] ['lambda nnrat]
                         ['point signed]]
                        (reciprocal
                         (nnrat-add (function/app 'hessian 'point) 'lambda)))})

(def definition-specs [lm-rate-spec])

;; Theorems -----------------------------------------------------------------

(def lm-rate-unfold-spec
  {:name 'optimization/levenberg-marquardt-rate-unfold :universes []
   :type (function/forall
          [['hessian hessian-type] ['lambda nnrat] ['point signed]]
          (equality nnrat (lm-rate 'hessian 'lambda 'point)
                    (reciprocal
                     (nnrat-add (function/app 'hessian 'point) 'lambda))))
   :value (function/lam [['hessian hessian-type] ['lambda nnrat]
                         ['point signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (lm-rate 'hessian 'lambda 'point)))})

(def theorem-specs [lm-rate-unfold-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Levenberg-Marquardt expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :levenberg-marquardt}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Levenberg-Marquardt declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.levenberg-marquardt))
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
