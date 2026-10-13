(ns rainbow.math.rational.nnrat.map-sum-respects
  "map-sum is a congruence for pointwise nnrat equivalence:

    nnrat/map-sum-respects-equivalence :
      (forall i, f i ~ g i) -> map-sum f is ~ map-sum g is

  Lets a per-term equivalence be rewritten underneath a finite sum -- the tool
  that applies map-sum-scale-right (and the per-term product reorder) inside the
  LP double sum.  List.rec induction: nil is reflexivity; cons is
  add-respects-equivalence on the head equivalence (hypothesis) and the tail
  equivalence (IH).  Polymorphic in the element type.  Native and axiom-free;
  chains nnrat-list-sum on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.list-sum :as ls]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- add-respects [l l-eq r r-eq same-l same-r]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l l-eq r r-eq same-l same-r))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- app [f x] (function/app f x))
(def nnrat-zero (function/const* 'nnrat/zero []))

(def map-sum-respects-spec
  {:name 'nnrat/map-sum-respects-equivalence :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
           ['hfg (function/forall [['i 'A]] (equiv (app 'f 'i) (app 'g 'i)))]
           ['is (list-of 'A)]]
          (equiv (map-sum 'A 'f 'is) (map-sum 'A 'g 'is)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
     ['hfg (function/forall [['i 'A]] (equiv (app 'f 'i) (app 'g 'i)))]
     ['is (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['ys (list-of 'A)]]
                   (equiv (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys)))
     ;; nil : 0 ~ 0
     (equiv-refl nnrat-zero)
     ;; cons head tail : (fh + Sf) ~ (gh + Sg)
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (equiv (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail))]]
      (add-respects (app 'f 'head) (app 'g 'head)
                    (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
                    (app 'hfg 'head) 'ih))
     'is))})

(def definition-specs [])
(def theorem-specs [map-sum-respects-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ls/extend-environment
      (support/extend-with :nnrat-map-sum-respects
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
