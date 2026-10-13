(ns rainbow.math.finite.markov-residual-mixture-bound
  "Markov-facing interface for the finite residual mixture inequality."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.weighted-sum-scaled-bound :as scaled]))

(def U [:param 'u])
(def type-u [:sort [:succ U]])
(defn- c [n] (f/const* n []))
(def nnrat (c 'nnrat/NonnegativeRational))
(defn- list-of [A] (f/app (f/const* 'data/List [[:succ U]]) A))
(defn- sum [A m xs] (f/app (f/const* 'nnrat/map-sum [U]) A m xs))
(defn- mul [a b] (f/app (c 'nnrat/multiply) a b))
(defn- le [a b] (f/app (c 'nnrat/at-most) a b))
(def spec
  {:name 'markov/nnrat-finite-residual-mixture-bound
   :universes ['u]
   :type (f/forall
          [['S type-u] ['weights (f/arrow 'S nnrat)]
           ['row-distance (f/arrow 'S nnrat)] ['rho nnrat]
           ['row-bound (f/forall [['x 'S]]
                                  (le (f/app 'row-distance 'x) 'rho))]
           ['residual-indexes (list-of 'S)]]
          (le (sum 'S (f/lam [['x 'S]]
                              (mul (f/app 'weights 'x)
                                   (f/app 'row-distance 'x)))
                   'residual-indexes)
              (mul (sum 'S 'weights 'residual-indexes) 'rho)))
   :value
   (f/lam
    [['S type-u] ['weights (f/arrow 'S nnrat)]
     ['row-distance (f/arrow 'S nnrat)] ['rho nnrat]
     ['row-bound (f/forall [['x 'S]]
                           (le (f/app 'row-distance 'x) 'rho))]
     ['residual-indexes (list-of 'S)]]
    (f/app (f/const* 'nnrat/weighted-sum-scaled-at-most [U])
           'S 'weights 'row-distance 'rho 'row-bound 'residual-indexes))})

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.weighted-sum-scaled-bound])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-residual-mixture-bound [spec])))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-residual-mixture-bound))
(defn theorem-ids [env] (support/spec-ids env [spec]))
