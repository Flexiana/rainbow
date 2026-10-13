(ns rainbow.math.finite.markov-mixture-statement
  "Formal target for the finite residual-mixture inequality used by Dobrushin.

  This is deliberately a proposition declaration: the finite sum inequality is
  not claimed until its constructive proof is registered." 
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-dobrushin-kernel :as coefficient]))

(def U [:param 'u])
(defn- c [name] (f/const* name []))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (c 'nnrat/NonnegativeRational))
(def parameters (conj coefficient/base-binders ['rho nnrat] ['weighted-sum nnrat] ['weight-total nnrat]))

(def mixture-inequality-spec
  {:name 'markov/nnrat-finite-mixture-bound
   :kind :definition :universes ['u]
   :type (f/forall parameters 'Prop)
   :value
   (f/lam parameters
    (f/forall []
      (f/app (c 'nnrat/at-most)
             'weighted-sum
             (f/app (c 'nnrat/multiply) 'rho 'weight-total))))})

(def definition-specs [mixture-inequality-spec])
(def theorem-specs [])
(defn extend-environment [env]
  (-> env coefficient/extend-environment
      (support/extend-with :finite-markov-mixture-statement definition-specs)))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
