(ns rainbow.algorithms.proofs.ahof.weighted-sum
  "AHoF O66 Weighted Sum Method (multi-objective scalarization): collapse several
  objectives into one scalar by a weighted sum, then optimize the scalar:

      scalarize w1 f1 w2 f2 = w1 * f1 + w2 * f2.

  With balanced weights 1/2, 1/2 on objectives 1/2, 3/4 the scalarized value is 5/8;
  with weight only on the first objective (weights 1, 0) it is the first objective
  1/2, so the weights genuinely steer the aggregate. Values are proved by cross-
  product equivalence. Proved native and axiom-free.

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.weighted-sum`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
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
(def half (make-rational 1 1))            ; 1/2
(def three-quarters (make-rational 3 3))  ; 3/4
(def five-eighths (make-rational 5 7))    ; 5/8

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

(defn- scalarize [w1 f1 w2 f2]
  (function/app (function/const* 'weighted-sum/scalarize []) w1 f1 w2 f2))

(def scalarize-spec
  {:name 'weighted-sum/scalarize :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
                        (nnrat-add (nnrat-multiply 'w1 'f1)
                                   (nnrat-multiply 'w2 'f2)))})

(def balanced-spec
  {:name 'weighted-sum/balanced :kind :definition :universes [] :type nnrat
   :value (scalarize half half half three-quarters)})
(def objective-one-only-spec
  {:name 'weighted-sum/objective-one-only :kind :definition :universes [] :type nnrat
   :value (scalarize nnrat-one half nnrat-zero three-quarters)})

(def definition-specs [scalarize-spec balanced-spec objective-one-only-spec])

(def scalarize-unfold-spec
  {:name 'weighted-sum/scalarize-unfold :universes []
   :type (function/forall [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
                          (equality nnrat (scalarize 'w1 'f1 'w2 'f2)
                                    (nnrat-add (nnrat-multiply 'w1 'f1)
                                               (nnrat-multiply 'w2 'f2))))
   :value (function/lam [['w1 nnrat] ['f1 nnrat] ['w2 nnrat] ['f2 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (scalarize 'w1 'f1 'w2 'f2)))})

;; Balanced weights give 5/8.
(def balanced-is-five-eighths-spec
  {:name 'weighted-sum/balanced-is-five-eighths :universes []
   :type (nnrat-equivalent (function/const* 'weighted-sum/balanced []) five-eighths)
   :value (equivalent-cross (function/const* 'weighted-sum/balanced []) five-eighths)})

;; Weight only on the first objective returns that objective, 1/2.
(def objective-one-is-half-spec
  {:name 'weighted-sum/objective-one-is-half :universes []
   :type (nnrat-equivalent (function/const* 'weighted-sum/objective-one-only []) half)
   :value (equivalent-cross (function/const* 'weighted-sum/objective-one-only []) half)})

(def weighted-sum-spec
  (let [bal (:type balanced-is-five-eighths-spec)
        obj (:type objective-one-is-half-spec)]
    {:name 'weighted-sum/weighted-sum :universes []
     :type (proposition/conjunction bal obj)
     :value (function/app (function/const* 'proposition/conjoin []) bal obj
                          (function/const* 'weighted-sum/balanced-is-five-eighths [])
                          (function/const* 'weighted-sum/objective-one-is-half []))}))

(def theorem-specs
  [scalarize-unfold-spec balanced-is-five-eighths-spec objective-one-is-half-spec
   weighted-sum-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-weighted-sum
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
