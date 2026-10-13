(ns rainbow.math.rational.nnrat.convex-multi-point
  "Finite nonnegative-weighted combinations preserve global value bounds:

      sum_i (w i * m)   <= sum_i (w i * v i)   when forall i, m <= v i
      sum_i (w i * v i) <= sum_i (w i * Mx)    when forall i, v i <= Mx

  These are the N-point convexity / averaging brackets without a normalization
  assumption on the weights.  Each proof first uses nnrat/multiply-monotone to
  lift the global bound through the nonnegative weight at one index, then uses
  nnrat/map-sum-monotone to lift those pointwise bounds through the finite sum.
  Polymorphic in the index type.  Native and axiom-free; chains nnrat-list-sum
  and nnrat-multiply-monotone on D63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.list-sum :as ls]
            [rainbow.math.rational.nnrat.multiply-monotone :as mm]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- rmul [l r]
  (function/app (function/const* 'nnrat/multiply []) l r))
(defn- rat-le [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-monotone [A f g hfg xs]
  (function/app (function/const* 'nnrat/map-sum-monotone [U]) A f g hfg xs))
(defn- multiply-monotone [c a b h]
  (function/app (function/const* 'nnrat/multiply-monotone []) c a b h))

(defn- weighted-value-map [w v]
  (function/lam [['i 'A]]
                (rmul (function/app w 'i) (function/app v 'i))))

(defn- weighted-bound-map [w bound]
  (function/lam [['i 'A]]
                (rmul (function/app w 'i) bound)))

;; A global lower bound remains a lower bound after termwise weighting and summing.
(def weighted-combo-at-least-spec
  {:name 'nnrat/weighted-combo-at-least :universes ['u]
   :type (function/forall
          [['A type-u]
           ['w (function/arrow 'A nnrat)]
           ['v (function/arrow 'A nnrat)]
           ['m nnrat]
           ['hm (function/forall
                 [['i 'A]]
                 (rat-le 'm (function/app 'v 'i)))]
           ['idx (list-of 'A)]]
          (rat-le (map-sum 'A (weighted-bound-map 'w 'm) 'idx)
                  (map-sum 'A (weighted-value-map 'w 'v) 'idx)))
   :value
   (function/lam
    [['A type-u]
     ['w (function/arrow 'A nnrat)]
     ['v (function/arrow 'A nnrat)]
     ['m nnrat]
     ['hm (function/forall
           [['i 'A]]
           (rat-le 'm (function/app 'v 'i)))]
     ['idx (list-of 'A)]]
    (map-sum-monotone
     'A (weighted-bound-map 'w 'm) (weighted-value-map 'w 'v)
     (function/lam
      [['i 'A]]
      (multiply-monotone (function/app 'w 'i)
                         'm (function/app 'v 'i)
                         (function/app 'hm 'i)))
     'idx))})

;; A global upper bound remains an upper bound after termwise weighting and summing.
(def weighted-combo-at-most-spec
  {:name 'nnrat/weighted-combo-at-most :universes ['u]
   :type (function/forall
          [['A type-u]
           ['w (function/arrow 'A nnrat)]
           ['v (function/arrow 'A nnrat)]
           ['Mx nnrat]
           ['hMx (function/forall
                  [['i 'A]]
                  (rat-le (function/app 'v 'i) 'Mx))]
           ['idx (list-of 'A)]]
          (rat-le (map-sum 'A (weighted-value-map 'w 'v) 'idx)
                  (map-sum 'A (weighted-bound-map 'w 'Mx) 'idx)))
   :value
   (function/lam
    [['A type-u]
     ['w (function/arrow 'A nnrat)]
     ['v (function/arrow 'A nnrat)]
     ['Mx nnrat]
     ['hMx (function/forall
            [['i 'A]]
            (rat-le (function/app 'v 'i) 'Mx))]
     ['idx (list-of 'A)]]
    (map-sum-monotone
     'A (weighted-value-map 'w 'v) (weighted-bound-map 'w 'Mx)
     (function/lam
      [['i 'A]]
      (multiply-monotone (function/app 'w 'i)
                         (function/app 'v 'i) 'Mx
                         (function/app 'hMx 'i)))
     'idx))})

(def definition-specs [])
(def theorem-specs
  [weighted-combo-at-least-spec weighted-combo-at-most-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ls/extend-environment
      mm/extend-environment
      (support/extend-with :nnrat-convex-multi-point
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
