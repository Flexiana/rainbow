(ns rainbow.math.rational.nnrat.map-sum-scale
  "Scalar pulls through a finite nnrat sum (scalar on the right), up to nnrat
  equivalence (~):

    nnrat/map-sum-scale-right : (map-sum f is) * c  ~  map-sum (\\i. f i * c) is

  The distributivity congruence (with Fubini) that moves a per-term factor in and
  out of the LP double sum.  Right-multiplication is used deliberately so the
  proof needs only the installed right-distributivity (a+b)*c ~ a*c + b*c; the
  nil case 0*c ~ 0 reduces to eq-nat 0 0 (nat-multiply reduces 0*X to 0 on the
  left) so a bare nat reflexivity closes it -- no commutativity and no identities
  module, hence no clash on the nnrat/add-commutative or nnrat/multiply-one-left
  aliases (each defined by several modules).  List.rec induction; polymorphic in
  the element type.  Native and axiom-free; chains nnrat-map-sum-additive,
  nnrat-distributive on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.map-sum-additive :as ma]
            [rainbow.math.rational.nnrat.distributive :as dist]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- rmul [l r] (function/app (function/const* 'nnrat/multiply []) l r))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l l-eq r r-eq same-l same-r]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l l-eq r r-eq same-l same-r))
(defn- dist-right [a b m] (function/app (function/const* 'nnrat/multiply-distributes-add-right []) a b m))
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def type-level [:succ [:zero]])
(def nat-refl-zero
  (function/app (function/const* 'equality/reflexive [type-level]) nat zero-nat))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- app [f x] (function/app f x))

(defn- scale-map-right [f c] (function/lam [['i 'A]] (rmul (app f 'i) c)))

(def map-sum-scale-right-spec
  {:name 'nnrat/map-sum-scale-right :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)] ['c nnrat] ['is (list-of 'A)]]
          (equiv (rmul (map-sum 'A 'f 'is) 'c)
                 (map-sum 'A (scale-map-right 'f 'c) 'is)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['c nnrat] ['is (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['ys (list-of 'A)]]
                   (equiv (rmul (map-sum 'A 'f 'ys) 'c)
                          (map-sum 'A (scale-map-right 'f 'c) 'ys)))
     ;; nil : 0 * c ~ 0  (reduces to eq-nat 0 0)
     nat-refl-zero
     ;; cons head tail : (fh + St) * c ~ (fh*c) + Rt
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (equiv (rmul (map-sum 'A 'f 'tail) 'c)
                   (map-sum 'A (scale-map-right 'f 'c) 'tail))]]
      (let [fh (app 'f 'head)
            st (map-sum 'A 'f 'tail)
            rt (map-sum 'A (scale-map-right 'f 'c) 'tail)]
        (equiv-trans (rmul (radd fh st) 'c)
                     (radd (rmul fh 'c) (rmul st 'c))
                     (radd (rmul fh 'c) rt)
                     (dist-right fh st 'c)
                     (add-respects (rmul fh 'c) (rmul fh 'c) (rmul st 'c) rt
                                   (equiv-refl (rmul fh 'c)) 'ih))))
     'is))})

(def definition-specs [])
(def theorem-specs [map-sum-scale-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ma/extend-environment
      dist/extend-environment
      (support/extend-with :nnrat-map-sum-scale
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
