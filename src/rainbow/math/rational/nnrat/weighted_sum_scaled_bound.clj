(ns rainbow.math.rational.nnrat.weighted-sum-scaled-bound
  "Compose the finite weighted-sum bound with right-scaling of a sum."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.weighted-sum-bound :as bound]
            [rainbow.math.rational.nnrat.weighted-sum-scaling :as scaling]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [n] (f/const* n []))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- list-of [A] (f/app (f/const* 'data/List [[:succ U]]) A))
(defn- sum [A m xs] (f/app (f/const* 'nnrat/map-sum [U]) A m xs))
(defn- mul [a b] (f/app (c 'nnrat/multiply) a b))
(defn- equiv [a b] (f/app (c 'nnrat/equivalent) a b))
(defn- le [a b] (f/app (c 'nnrat/at-most) a b))
(def spec
  {:name 'nnrat/weighted-sum-scaled-at-most
   :universes ['u]
   :type
   (f/forall
    [['A type-u] ['weight (f/arrow 'A nnrat)] ['distance (f/arrow 'A nnrat)]
     ['rho nnrat]
     ['pointwise (f/forall [['x 'A]]
                            (le (f/app 'distance 'x) 'rho))]
     ['source (list-of 'A)]]
    (le (sum 'A (f/lam [['x 'A]] (mul (f/app 'weight 'x)
                                      (f/app 'distance 'x))) 'source)
        (mul (sum 'A 'weight 'source) 'rho)))
   :value
   (f/lam
    [['A type-u] ['weight (f/arrow 'A nnrat)] ['distance (f/arrow 'A nnrat)]
     ['rho nnrat]
     ['pointwise (f/forall [['x 'A]] (le (f/app 'distance 'x) 'rho))]
     ['source (list-of 'A)]]
    (let [lhs (sum 'A (f/lam [['x 'A]]
                              (mul (f/app 'weight 'x) (f/app 'distance 'x)))
                   'source)
          summed-rho (sum 'A (f/lam [['x 'A]]
                                     (mul (f/app 'weight 'x) 'rho)) 'source)
          scaled (mul (sum 'A 'weight 'source) 'rho)
          step (f/app (f/const* 'nnrat/weighted-sum-at-most [U])
                      'A 'weight 'distance 'rho 'pointwise 'source)
          bridge (f/app (f/const* 'nnrat/weighted-sum-scaling [U])
                        'A 'weight 'rho 'source)
          scaled-eq-summed bridge]
      (f/app (c 'nnrat/at-most-respects-equivalence)
             lhs lhs scaled summed-rho
             (f/app (c 'nnrat/equivalent-reflexive) lhs)
             scaled-eq-summed step)))} )

(defn extend-environment [env]
  (-> env bound/extend-environment
      scaling/extend-environment
      (support/extend-with :nnrat-weighted-sum-scaled-bound [spec])))
(defn theorem-ids [env] (support/spec-ids env [spec]))
