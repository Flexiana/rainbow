(ns rainbow.math.rational.nnrat.weighted-sum-scaling
  "Publicly named finite-sum scaling bridge for contraction proofs."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.map-sum-scale :as scale]))
(def U [:param 'u])
(def type-u [:sort [:succ U]])
(def nnrat (f/const* 'nnrat/NonnegativeRational []))
(def list-of (fn [A] (f/app (f/const* 'data/List [[:succ U]]) A)))
(defn- c [n] (f/const* n []))
(defn- sum [A m xs] (f/app (f/const* 'nnrat/map-sum [U]) A m xs))
(def spec
  {:name 'nnrat/weighted-sum-scaling
   :universes ['u]
   :type (f/forall [['A type-u] ['mapping (f/arrow 'A nnrat)] ['scalar nnrat] ['source (list-of 'A)]]
                   (f/app (c 'nnrat/equivalent)
                          (f/app (c 'nnrat/multiply) (sum 'A 'mapping 'source) 'scalar)
                          (sum 'A (f/lam [['x 'A]]
                                           (f/app (c 'nnrat/multiply) (f/app 'mapping 'x) 'scalar))
                               'source)))
   :value (f/lam [['A type-u] ['mapping (f/arrow 'A nnrat)] ['scalar nnrat] ['source (list-of 'A)]]
                 (f/app (f/const* 'nnrat/map-sum-scale-right [U]) 'A 'mapping 'scalar 'source))})
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.map-sum-scale])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :nnrat-weighted-sum-scaling [spec])))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.nnrat.weighted-sum-scaling))
(defn theorem-ids [env] (support/spec-ids env [spec]))
