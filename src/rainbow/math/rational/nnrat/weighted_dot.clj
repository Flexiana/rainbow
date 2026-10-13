(ns rainbow.math.rational.nnrat.weighted-dot
  "Weighted sum (dot product) of nonnegative-rational coordinate functions over
  an index list, and its monotonicity in the value coordinates:

    nnrat/weighted-sum A c x is       = sum_i (c i) * (x i)          over is : List A
    nnrat/weighted-sum-monotone       : (forall i, x i <= x' i)
                                        -> weighted-sum c x is <= weighted-sum c x' is

  This is the LP objective-bound engine: with nonnegative weights c, dominating
  the values coordinatewise (x <= x') dominates the weighted total -- the
  monotone direction behind c.x <= c.x' and, composed with a feasibility
  substitution, weak duality c.x <= b.y.

  Proof: nnrat/map-sum-monotone applied to the composite terms (c i)*(x i), whose
  termwise domination is nnrat/multiply-monotone (nonneg weight preserves <=).
  Polymorphic in the index type A.  Native and axiom-free; chains
  nnrat-list-sum and nnrat-multiply-monotone on d63."
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
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- rat-le [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-monotone [A f g hfg xs]
  (function/app (function/const* 'nnrat/map-sum-monotone [U]) A f g hfg xs))
(defn- multiply-monotone [c a b h]
  (function/app (function/const* 'nnrat/multiply-monotone []) c a b h))
(defn- weighted-sum [A c x is]
  (function/app (function/const* 'nnrat/weighted-sum [U]) A c x is))

;; the per-coordinate term c i * x i, as a mapping A -> nnrat
(defn- term-map [c x]
  (function/lam [['i 'A]] (rmul (function/app c 'i) (function/app x 'i))))

(def weighted-sum-spec
  {:name 'nnrat/weighted-sum :kind :definition :universes ['u] :transparency :reducible
   :type (function/forall
          [['A type-u] ['c (function/arrow 'A nnrat)] ['x (function/arrow 'A nnrat)]]
          (function/arrow (list-of 'A) nnrat))
   :value
   (function/lam
    [['A type-u] ['c (function/arrow 'A nnrat)] ['x (function/arrow 'A nnrat)]
     ['is (list-of 'A)]]
    (map-sum 'A (term-map 'c 'x) 'is))})

;; nonnegative weights: dominating the values coordinatewise dominates the total
(def weighted-sum-monotone-spec
  {:name 'nnrat/weighted-sum-monotone :universes ['u]
   :type (function/forall
          [['A type-u] ['c (function/arrow 'A nnrat)]
           ['x (function/arrow 'A nnrat)] ['x-hi (function/arrow 'A nnrat)]
           ['hx (function/forall [['i 'A]] (rat-le (function/app 'x 'i)
                                                   (function/app 'x-hi 'i)))]
           ['is (list-of 'A)]]
          (rat-le (weighted-sum 'A 'c 'x 'is) (weighted-sum 'A 'c 'x-hi 'is)))
   :value
   (function/lam
    [['A type-u] ['c (function/arrow 'A nnrat)]
     ['x (function/arrow 'A nnrat)] ['x-hi (function/arrow 'A nnrat)]
     ['hx (function/forall [['i 'A]] (rat-le (function/app 'x 'i)
                                             (function/app 'x-hi 'i)))]
     ['is (list-of 'A)]]
    (map-sum-monotone
     'A (term-map 'c 'x) (term-map 'c 'x-hi)
     ;; termwise: (c i)*(x i) <= (c i)*(x-hi i)  since x i <= x-hi i
     (function/lam [['i 'A]]
                   (multiply-monotone (function/app 'c 'i)
                                      (function/app 'x 'i) (function/app 'x-hi 'i)
                                      (function/app 'hx 'i)))
     'is))})

(def definition-specs [weighted-sum-spec])
(def theorem-specs [weighted-sum-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ls/extend-environment
      mm/extend-environment
      (support/extend-with :nnrat-weighted-dot
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
