(ns rainbow.math.rational.nnrat.weighted-map-sum-distance
  "Weighted distance lift using the canonical scalar scaling theorem."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.metric-separation :as metric]
            [rainbow.math.rational.nnrat.map-sum-distance :as sums]))
(def U [:param 'u])
(def nnrat sums/nnrat)
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- mul [a b] (app 'nnrat/multiply a b))
(defn- dist [a b] (app 'nnrat/distance a b))
(defn- sum [mapping] (poly 'nnrat/map-sum 'A mapping 'source))
(def spec
  (let [bindings (into sums/base-binders
                       [['weight (f/arrow 'A nnrat)]
                        ['source (f/app (f/const* 'data/List [[:succ U]]) 'A)]])
        weighted (fn [mapping]
                   (f/lam [['x 'A]] (mul (f/app 'weight 'x) (f/app mapping 'x))))
        radii (f/lam [['x 'A]]
                (mul (f/app 'weight 'x)
                     (dist (f/app 'left 'x) (f/app 'right 'x))))]
    {:name 'nnrat/weighted-map-sum-distance-bound :universes ['u]
     :type (f/forall bindings
             (app 'nnrat/at-most (dist (sum (weighted 'left)) (sum (weighted 'right)))
                  (sum radii)))
     :value (f/lam bindings
              (poly 'nnrat/map-sum-distance-bound-by
                    'A (weighted 'left) (weighted 'right) radii
                    (f/lam [['x 'A]]
                      (app 'nnrat/distance-multiply-left-bound
                           (f/app 'weight 'x) (f/app 'left 'x) (f/app 'right 'x)))
                    'source))}))
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.metric-separation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-weighted-map-sum-distance [spec])))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.weighted-map-sum-distance))
(defn theorem-ids [env] (support/spec-ids env [spec]))
