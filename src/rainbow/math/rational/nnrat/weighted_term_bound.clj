(ns rainbow.math.rational.nnrat.weighted-term-bound
  "Scalar weighted-term monotonicity for the finite mixture proof."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.multiply-monotone :as monotone]))
(defn- c [n] (f/const* n []))
(def nnrat (c 'nnrat/NonnegativeRational))
(def mul (fn [a b] (f/app (c 'nnrat/multiply) a b)))
(def spec
  {:name 'nnrat/weighted-term-at-most
   :universes []
   :type (f/forall [['weight nnrat] ['distance nnrat] ['rho nnrat]
                    ['h (f/app (c 'nnrat/at-most) 'distance 'rho)]]
                   (f/app (c 'nnrat/at-most) (mul 'weight 'distance)
                          (mul 'weight 'rho)))
   :value
   (f/lam [['weight nnrat] ['distance nnrat] ['rho nnrat]
           ['h (f/app (c 'nnrat/at-most) 'distance 'rho)]]
          (f/app (c 'nnrat/multiply-monotone) 'weight 'distance 'rho 'h))})
(def definition-specs [])
(def theorem-specs [spec])
(defn extend-environment [env]
  (-> env monotone/extend-environment
      (support/extend-with :nnrat-weighted-term-bound theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
