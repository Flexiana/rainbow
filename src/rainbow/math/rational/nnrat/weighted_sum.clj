(ns rainbow.math.rational.nnrat.weighted-sum
  "Universal monotonicity of a two-term nonnegative-rational weighted sum in its
  values -- the first composite guarantee assembled from the monotonicity
  foundation (nnrat/multiply-monotone + nnrat/add-monotone):

      wsum2 w0 w1 v0 v1 = w0*v0 + w1*v1

      wsum2-monotone : v0 <= v0' -> v1 <= v1'
                    -> wsum2 w0 w1 v0 v1 <= wsum2 w0 w1 v0' v1'   (all w0 w1 v..)

  i.e. raising either input value (weights fixed) never lowers the aggregate: the
  weighted sum respects dominance.  This universally upgrades the weighted-sum /
  weighted-average catalog family (composite metric, GP posterior mean, EKF/particle
  filter updates, Monte-Carlo mean), which the AHoF catalog exercised only on worked
  instances.  Proof is a direct composition: scale each term by its weight with
  nnrat/multiply-monotone, then combine the two ordered terms with the two-sided
  nnrat/add-monotone.

  Native and axiom-free; chains rainbow.math.rational.nnrat.multiply-monotone and
  rainbow.math.rational.nnrat.add-monotone (both on the d63 base)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.multiply-monotone :as mm]
            [rainbow.math.rational.nnrat.add-monotone :as am]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- rmul [c x] (function/app (function/const* 'nnrat/multiply []) c x))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- wsum2 [w0 w1 v0 v1]
  (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))

;; wsum2 w0 w1 v0 v1 = w0*v0 + w1*v1
(def wsum2-spec
  {:name 'nnrat/wsum2 :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
                        (radd (rmul 'w0 'v0) (rmul 'w1 'v1)))})

(def definition-specs [wsum2-spec])

;; v0<=v0' -> v1<=v1' -> wsum2 w0 w1 v0 v1 <= wsum2 w0 w1 v0' v1'
(def wsum2-monotone-spec
  {:name 'nnrat/wsum2-monotone :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat]
           ['v0 nnrat] ['v0-hi nnrat] ['v1 nnrat] ['v1-hi nnrat]
           ['h0 (rat-le 'v0 'v0-hi)] ['h1 (rat-le 'v1 'v1-hi)]]
          (rat-le (wsum2 'w0 'w1 'v0 'v1) (wsum2 'w0 'w1 'v0-hi 'v1-hi)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat]
     ['v0 nnrat] ['v0-hi nnrat] ['v1 nnrat] ['v1-hi nnrat]
     ['h0 (rat-le 'v0 'v0-hi)] ['h1 (rat-le 'v1 'v1-hi)]]
    (let [m0 (function/app (function/const* 'nnrat/multiply-monotone [])
                           'w0 'v0 'v0-hi 'h0)      ; w0*v0 <= w0*v0'
          m1 (function/app (function/const* 'nnrat/multiply-monotone [])
                           'w1 'v1 'v1-hi 'h1)]     ; w1*v1 <= w1*v1'
      (function/app (function/const* 'nnrat/add-monotone [])
                    (rmul 'w0 'v0) (rmul 'w0 'v0-hi)
                    (rmul 'w1 'v1) (rmul 'w1 'v1-hi)
                    m0 m1)))})

(def theorem-specs [wsum2-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      mm/extend-environment
      am/extend-environment
      (support/extend-with :nnrat-weighted-sum
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
