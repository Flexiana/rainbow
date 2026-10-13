(ns rainbow.math.rational.nnrat.map-sum-distance
  "Distance of finite NNRAT sums is bounded by the sum of distances.

  Sum the two additive-closeness inequalities termwise, distribute map-sum
  over addition up to rational equivalence, and recover the distance bound.
  This needs neither a triangle axiom nor a signed-distance bridge. The list
  may be empty or contain duplicates; no normalization is required."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distance :as distance]
            [rainbow.math.rational.nnrat.map-sum-additive :as additive]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(defn- list-of [A] (f/app (f/const* 'data/List [[:succ U]]) A))
(defn- add [a b] (app 'nnrat/add a b))
(defn- dist [a b] (app 'nnrat/distance a b))
(defn- le [a b] (app 'nnrat/at-most a b))
(defn- sum [mapping] (poly 'nnrat/map-sum 'A mapping 'source))

(def base-binders
  [['A type-u] ['left (f/arrow 'A nnrat)] ['right (f/arrow 'A nnrat)]])

(defn- pointwise-bound [radius]
  (f/forall [['x 'A]]
    (le (dist (f/app 'left 'x) (f/app 'right 'x)) (f/app radius 'x))))

(defn- summed-closeness [reverse?]
  (let [a (if reverse? 'right 'left)
        b (if reverse? 'left 'right)
        padded (f/lam [['x 'A]] (add (f/app b 'x) (f/app 'radius 'x)))
        left-close (le (f/app 'left 'x)
                       (add (f/app 'right 'x) (f/app 'radius 'x)))
        right-close (le (f/app 'right 'x)
                        (add (f/app 'left 'x) (f/app 'radius 'x)))
        both (app 'nnrat/additive-closeness-of-distance-at-most
                  (f/app 'left 'x) (f/app 'right 'x) (f/app 'radius 'x)
                  (f/app 'pointwise 'x))
        pointwise (f/lam [['x 'A]]
                    (app (if reverse? 'proposition/right 'proposition/left)
                         left-close right-close both))
        distributed (poly 'nnrat/map-sum-add 'A b 'radius 'source)
        total-radius (add (sum b) (sum 'radius))]
    (app 'nnrat/at-most-respects-equivalence
         (sum a) (sum a) total-radius (sum padded)
         (app 'nnrat/equivalent-reflexive (sum a))
         (app 'nnrat/equivalent-symmetric (sum padded) total-radius distributed)
         (poly 'nnrat/map-sum-monotone 'A a padded pointwise 'source))))

(def map-sum-distance-bound-by-spec
  (let [bindings (into base-binders
                       [['radius (f/arrow 'A nnrat)]
                        ['pointwise (pointwise-bound 'radius)]
                        ['source (list-of 'A)]])]
    {:name 'nnrat/map-sum-distance-bound-by :universes ['u]
     :type (f/forall bindings
             (le (dist (sum 'left) (sum 'right)) (sum 'radius)))
     :value (f/lam bindings
              (app 'nnrat/distance-at-most-of-additive-closeness
                   (sum 'left) (sum 'right) (sum 'radius)
                   (summed-closeness false) (summed-closeness true)))}))

(def map-sum-distance-bound-spec
  (let [bindings (conj base-binders ['source (list-of 'A)])
        distances (f/lam [['x 'A]]
                    (dist (f/app 'left 'x) (f/app 'right 'x)))]
    {:name 'nnrat/map-sum-distance-bound :universes ['u]
     :type (f/forall bindings
             (le (dist (sum 'left) (sum 'right)) (sum distances)))
     :value (f/lam bindings
              (poly 'nnrat/map-sum-distance-bound-by
                    'A 'left 'right distances
                    (f/lam [['x 'A]]
                      (app 'nnrat/at-most-reflexive
                           (dist (f/app 'left 'x) (f/app 'right 'x))))
                    'source))}))


(def theorem-specs [map-sum-distance-bound-by-spec map-sum-distance-bound-spec])
(defn extend-unweighted-environment [env]
  (-> env distance/extend-environment additive/extend-environment
      (support/extend-with :nnrat-map-sum-distance [map-sum-distance-bound-by-spec])))
(defn extend-environment [env]
  (-> env extend-unweighted-environment
      (support/extend-with :nnrat-map-sum-distance [map-sum-distance-bound-spec])))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
