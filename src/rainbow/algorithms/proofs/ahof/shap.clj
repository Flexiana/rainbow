(ns rainbow.algorithms.proofs.ahof.shap
  "AHoF V55 SHAP Values: attribute a prediction to features as a weighted sum of feature\n  contributions (Shapley-weighted); attribution w0 c0 w1 c1 = w0*c0 + w1*c1. Proved\n  native and axiom-free (worked values by cross-product equivalence).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.shap`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def half (make-rational 1 1))
(def three-quarters (make-rational 3 3))
(def five-eighths (make-rational 5 7))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-multiply [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- op [w0 x0 w1 x1] (function/app (function/const* 'shap/attribution []) w0 x0 w1 x1))

(def op-spec
  {:name 'shap/attribution :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                        (nnrat-add (nnrat-multiply 'w0 'x0)
                                   (nnrat-multiply 'w1 'x1)))})

(def balanced-spec
  {:name 'shap/balanced :kind :definition :universes [] :type nnrat
   :value (op half half half three-quarters)})
(def single-spec
  {:name 'shap/single :kind :definition :universes [] :type nnrat
   :value (op nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [op-spec balanced-spec single-spec])

(def op-unfold-spec
  {:name 'shap/attribution-unfold :universes []
   :type (function/forall [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                          (equality nnrat (op 'w0 'x0 'w1 'x1)
                                    (nnrat-add (nnrat-multiply 'w0 'x0)
                                               (nnrat-multiply 'w1 'x1))))
   :value (function/lam [['w0 nnrat] ['x0 nnrat] ['w1 nnrat] ['x1 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (op 'w0 'x0 'w1 'x1)))})

(def balanced-is-five-eighths-spec
  {:name 'shap/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'shap/balanced []) five-eighths)
   :value (equivalent-cross (function/const* 'shap/balanced []) five-eighths)})

(def single-is-first-spec
  {:name 'shap/single-is-first :universes []
   :type (nnrat-equivalent (function/const* 'shap/single []) half)
   :value (equivalent-cross (function/const* 'shap/single []) half)})

(def combined-spec
  (let [a (:type balanced-is-five-eighths-spec) b (:type single-is-first-spec)]
    {:name 'shap/combined :universes []
     :type (proposition/conjunction a b)
     :value (function/app (function/const* 'proposition/conjoin []) a b
                          (function/const* 'shap/balanced-is-five-eighths [])
                          (function/const* 'shap/single-is-first []))}))

(def theorem-specs [op-unfold-spec balanced-is-five-eighths-spec single-is-first-spec combined-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-shap (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.shap))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
