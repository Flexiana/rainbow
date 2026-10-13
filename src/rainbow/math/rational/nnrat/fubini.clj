(ns rainbow.math.rational.nnrat.fubini
  "Fubini / double-sum swap for finite nnrat sums, up to nnrat equivalence (~):

    nnrat/map-sum-swap :
      sum_{i in is} sum_{j in js} F i j  ~  sum_{j in js} sum_{i in is} F i j

  i.e. map-sum A (\\i. map-sum B (F i) js) is ~ map-sum B (\\j. map-sum A (\\i. F i j) is) js.

  The keystone that turns the weighted-sum monotone legs into an actual LP
  weak-duality bound c.x <= b.y (via (Aᵀy).x = y.(Ax)), and the reusable
  interchange behind expectation-of-sum, covariance, and any rectangular
  double accumulation.

  Proof: List.rec induction on the outer list `is`.
    nil  : LHS = 0; RHS = sum_j (empty inner sum) = sum_j 0 ~ 0  (map-sum-zero).
    cons : LHS = (sum_j F h j) + (inner IH); RHS's outer mapping splits by the
           inner cons recurrence into (F h j) + rest, and map-sum-add pushes that
           out to (sum_j F h j) + (sum_j rest); the IH identifies (inner IH) with
           (sum_j rest); add-respects-equivalence recombines.
  Polymorphic in both index types.  Native and axiom-free; chains
  nnrat-map-sum-additive on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.map-sum-additive :as ma]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- cons-of [element head tail]
  (function/app (function/const* 'data/cons [data-level]) element head tail))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-sym [l r same] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r same))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l l-eq r r-eq same-l same-r]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l l-eq r r-eq same-l same-r))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- map-sum-zero [A xs]
  (function/app (function/const* 'nnrat/map-sum-zero [U]) A xs))
(defn- map-sum-add [A f g xs]
  (function/app (function/const* 'nnrat/map-sum-add [U]) A f g xs))
(defn- app [f x] (function/app f x))

(def map-sum-swap-spec
  {:name 'nnrat/map-sum-swap :universes ['u]
   :type (function/forall
          [['A type-u] ['B type-u]
           ['F (function/arrow 'A (function/arrow 'B nnrat))]
           ['is (list-of 'A)] ['js (list-of 'B)]]
          (equiv (map-sum 'A (function/lam [['i 'A]] (map-sum 'B (app 'F 'i) 'js)) 'is)
                 (map-sum 'B (function/lam [['j 'B]]
                                           (map-sum 'A (function/lam [['i 'A]] (app (app 'F 'i) 'j)) 'is))
                          'js)))
   :value
   (function/lam
    [['A type-u] ['B type-u]
     ['F (function/arrow 'A (function/arrow 'B nnrat))]
     ['is (list-of 'A)] ['js (list-of 'B)]]
    (let [ISf (function/lam [['i 'A]] (map-sum 'B (app 'F 'i) 'js))
          inner (fn [ys] (function/lam [['j 'B]]
                                       (map-sum 'A (function/lam [['i 'A]] (app (app 'F 'i) 'j)) ys)))
          zeromap-B (function/lam [['j 'B]] nnrat-zero)
          motive (function/lam [['ys (list-of 'A)]]
                               (equiv (map-sum 'A ISf 'ys)
                                      (map-sum 'B (inner 'ys) 'js)))
          nil-case (equiv-sym (map-sum 'B zeromap-B 'js) nnrat-zero (map-sum-zero 'B 'js))
          cons-case
          (function/lam
           [['head 'A] ['tail (list-of 'A)]
            ['ih (equiv (map-sum 'A ISf 'tail) (map-sum 'B (inner 'tail) 'js))]]
           (let [P (map-sum 'B (app 'F 'head) 'js)
                 Q (map-sum 'A ISf 'tail)
                 RESTt (inner 'tail)
                 R (map-sum 'B RESTt 'js)
                 RHS (map-sum 'B (inner (cons-of 'A 'head 'tail)) 'js)
                 add-lemma (map-sum-add 'B (app 'F 'head) RESTt 'js)]  ; RHS ~ (P + R)
             (equiv-trans (radd P Q) (radd P R) RHS
                          (add-respects P P Q R (equiv-refl P) 'ih)
                          (equiv-sym RHS (radd P R) add-lemma))))]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive nil-case cons-case 'is)))})

(def definition-specs [])
(def theorem-specs [map-sum-swap-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ma/extend-environment
      (support/extend-with :nnrat-fubini
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
