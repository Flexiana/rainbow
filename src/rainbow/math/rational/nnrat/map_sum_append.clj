(ns rainbow.math.rational.nnrat.map-sum-append
  "Finite nnrat sums split over list concatenation, up to nnrat equivalence (~):

    nnrat/map-sum-append : map-sum f (append xs ys) ~ map-sum f xs + map-sum f ys

  The block/partition-decomposition law: the sum over a concatenated index list is
  the sum of the block sums.  Reusable for LP column generation (append new
  columns), expectation over a partitioned sample space, and any divide-and-sum.
  Proof: List.rec induction on xs (list/append reduces definitionally on its
  left argument); nil case is add-zero-left, cons case is add-associative plus
  add-respects-equivalence and the IH.  Polymorphic in the element type.
  Native and axiom-free; chains nnrat-list-sum, nnrat-additive-reassociation,
  nnrat-identities on d63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.list-sum :as ls]
            [rainbow.math.rational.nnrat.additive-reassociation :as ar]
            [rainbow.math.rational.nnrat.identities :as ident]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- list-of [element] (function/app (function/const* 'data/List [data-level]) element))
(defn- appendl [A xs ys] (function/app (function/const* 'list/append [data-level]) A xs ys))
(defn- cons-of [element head tail]
  (function/app (function/const* 'data/cons [data-level]) element head tail))
(defn- nil-of [element] (function/app (function/const* 'data/nil [data-level]) element))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- equiv [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- equiv-trans [l m r p q]
  (function/app (function/const* 'nnrat/equivalent-transitive []) l m r p q))
(defn- add-respects [l l-eq r r-eq same-l same-r]
  (function/app (function/const* 'nnrat/add-respects-equivalence []) l l-eq r r-eq same-l same-r))
(defn- add-assoc [a b c] (function/app (function/const* 'nnrat/add-associative []) a b c))
(defn- add-zero-left [v] (function/app (function/const* 'nnrat/add-zero-left []) v))
(defn- map-sum [A f xs] (function/app (function/const* 'nnrat/map-sum [U]) A f xs))
(defn- app [f x] (function/app f x))

(def map-sum-append-spec
  {:name 'nnrat/map-sum-append :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)]
           ['xs (list-of 'A)] ['ys (list-of 'A)]]
          (equiv (map-sum 'A 'f (appendl 'A 'xs 'ys))
                 (radd (map-sum 'A 'f 'xs) (map-sum 'A 'f 'ys))))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)]
     ['xs (list-of 'A)] ['ys (list-of 'A)]]
    ;; induction on xs (list/append recurses on xs); ys is free in the motive
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['zs (list-of 'A)]]
                   (equiv (map-sum 'A 'f (appendl 'A 'zs 'ys))
                          (radd (map-sum 'A 'f 'zs) (map-sum 'A 'f 'ys))))
     ;; nil : map-sum f ys ~ (0 + map-sum f ys)
     (equiv-sym (radd (map-sum 'A 'f (nil-of 'A)) (map-sum 'A 'f 'ys))
                (map-sum 'A 'f 'ys)
                (add-zero-left (map-sum 'A 'f 'ys)))
     ;; cons head tail : (fh + A_t) ~ ((fh + S_t) + S_y)
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (equiv (map-sum 'A 'f (appendl 'A 'tail 'ys))
                   (radd (map-sum 'A 'f 'tail) (map-sum 'A 'f 'ys)))]]
      (let [fh (app 'f 'head)
            at (map-sum 'A 'f (appendl 'A 'tail 'ys))
            st (map-sum 'A 'f 'tail)
            sy (map-sum 'A 'f 'ys)]
        (equiv-trans (radd fh at)
                     (radd fh (radd st sy))
                     (radd (radd fh st) sy)
                     (add-respects fh fh at (radd st sy) (equiv-refl fh) 'ih)
                     (equiv-sym (radd (radd fh st) sy) (radd fh (radd st sy))
                                (add-assoc fh st sy)))))
     'xs))})

(def definition-specs [])
(def theorem-specs [map-sum-append-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.list-sum rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.nnrat.identities])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-map-sum-append (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.map-sum-append))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
