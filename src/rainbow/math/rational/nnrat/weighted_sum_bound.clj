(ns rainbow.math.rational.nnrat.weighted-sum-bound
  "Finite-list lift of weighted-term monotonicity."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.bellman-monotone :as sums]
            [rainbow.math.rational.nnrat.weighted-term-bound :as term]))
(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [n] (f/const* n []))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- map-sum [A m xs] (f/app (f/const* 'list/nnrat-map-sum [U]) A m xs))
(defn- mul [a b] (f/app (c 'nnrat/multiply) a b))
(def spec
  {:name 'nnrat/weighted-sum-at-most
   :universes ['u]
   :type (f/forall
          [['A type-u] ['weight (f/arrow 'A nnrat)]
           ['distance (f/arrow 'A nnrat)] ['rho nnrat]
           ['pointwise (f/forall [['x 'A]]
                                  (f/app (c 'nnrat/at-most)
                                         (f/app 'distance 'x) 'rho))]
           ['source (f/app (f/const* 'data/List [[:succ U]]) 'A)]]
          (f/app (c 'nnrat/at-most)
                 (map-sum 'A (f/lam [['x 'A]] (mul (f/app 'weight 'x) (f/app 'distance 'x))) 'source)
                 (map-sum 'A (f/lam [['x 'A]] (mul (f/app 'weight 'x) 'rho)) 'source)))
   :value
   (f/lam
    [['A type-u] ['weight (f/arrow 'A nnrat)] ['distance (f/arrow 'A nnrat)] ['rho nnrat]
     ['pointwise (f/forall [['x 'A]]
                            (f/app (c 'nnrat/at-most) (f/app 'distance 'x) 'rho))]
     ['source (f/app (f/const* 'data/List [[:succ U]]) 'A)]]
    (f/app (f/const* 'list/nnrat-map-sum-monotone [U])
           'A
           (f/lam [['x 'A]] (mul (f/app 'weight 'x) (f/app 'distance 'x)))
           (f/lam [['x 'A]] (mul (f/app 'weight 'x) 'rho))
           (f/lam [['x 'A]]
             (f/app (c 'nnrat/weighted-term-at-most)
                    (f/app 'weight 'x) (f/app 'distance 'x) 'rho
                    (f/app 'pointwise 'x)))
           'source))})
(defn extend-environment [env]
  (-> env sums/extend-environment term/extend-environment
      (support/extend-with :nnrat-weighted-sum-bound [spec])))
(defn theorem-ids [env] (support/spec-ids env [spec]))
