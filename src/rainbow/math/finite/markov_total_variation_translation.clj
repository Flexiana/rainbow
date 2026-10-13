(ns rainbow.math.finite.markov-total-variation-translation
  "Common finite mass cancels from L1 and normalized total variation.

  This removes a shared component before bounding the remaining mass in the
  Dobrushin proof. No normalization or disjointness premise is needed here."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-total-variation-bound :as bound]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distance-translation :as scalar]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- shifted [mass]
  (f/lam [['state 'S]]
    (f/app (c 'nnrat/add) (f/app mass 'state) (f/app 'common 'state))))
(defn- l1 [left right]
  (poly 'markov/nnrat-total-variation 'S 'states left right))
(defn- tv [left right]
  (poly 'markov/nnrat-normalized-total-variation 'S 'states left right))
(defn- eqv [a b] (f/app (c 'nnrat/equivalent) a b))
(def bindings (conj bound/mass-binders ['common (f/arrow 'S nnrat)]))

(def total-variation-common-mass-spec
  {:name 'markov/nnrat-total-variation-common-mass :universes ['u]
   :type (f/forall bindings
           (eqv (l1 (shifted 'left) (shifted 'right)) (l1 'left 'right)))
   :value
   (f/lam bindings
     (poly 'nnrat/map-sum-respects-equivalence
           'S
           (f/lam [['state 'S]]
             (f/app (c 'nnrat/distance)
                    (f/app (shifted 'left) 'state) (f/app (shifted 'right) 'state)))
           (f/lam [['state 'S]]
             (f/app (c 'nnrat/distance) (f/app 'left 'state) (f/app 'right 'state)))
           (f/lam [['state 'S]]
             (f/app (c 'nnrat/distance-add-right)
                    (f/app 'left 'state) (f/app 'right 'state) (f/app 'common 'state)))
           (poly 'finset-data/enumeration 'S 'states)))})

(def normalized-total-variation-common-mass-spec
  {:name 'markov/nnrat-normalized-total-variation-common-mass :universes ['u]
   :type (f/forall bindings
           (eqv (tv (shifted 'left) (shifted 'right)) (tv 'left 'right)))
   :value
   (f/lam bindings
     (f/app (c 'nnrat/multiply-respects-equivalence)
            (c 'nnrat/half) (c 'nnrat/half)
            (l1 (shifted 'left) (shifted 'right)) (l1 'left 'right)
            (f/app (c 'nnrat/equivalent-reflexive) (c 'nnrat/half))
            (poly 'markov/nnrat-total-variation-common-mass
                  'S 'states 'left 'right 'common)))})

(def theorem-specs [total-variation-common-mass-spec
                    normalized-total-variation-common-mass-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-total-variation-bound rainbow.math.rational.nnrat.distance-translation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-total-variation-translation theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-total-variation-translation))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
