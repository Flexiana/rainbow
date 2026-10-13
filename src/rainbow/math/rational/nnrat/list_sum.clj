(ns rainbow.math.rational.nnrat.list-sum
  "Finite sum of an nnrat-valued map over a list, and its monotonicity -- the
  n-ary generalization of nnrat/wsum2-monotone and the fold-level induction the
  scout flagged as the missing piece for dot-product / LP bounds:

    nnrat/map-sum A f xs        = f x0 + f x1 + ... + f xn   (empty sum = 0)
    nnrat/map-sum-monotone      : (forall x, f x <= g x) -> map-sum f xs <= map-sum g xs

  Termwise domination lifts through a finite sum.  This is the reusable engine
  behind: expected-value monotonicity (sum of weighted rewards), norm/penalty
  bounds (sum of nonneg terms), and dot-product monotonicity c.x <= c.x' when x
  is dominated coordinatewise -- hence LP weak-duality-style objective bounds.

  Proof: native List.rec fold of nnrat/add from nnrat/zero; monotonicity is a
  List.rec induction whose nil case is at-most-reflexive 0 and whose cons case is
  nnrat/add-monotone (f head <= g head, tail-sum <= tail-sum by the IH).
  Polymorphic in the element type A.  Native and axiom-free; chains
  nnrat-add-monotone on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.add-monotone :as am]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))
(defn- cons-of [element head tail]
  (function/app (function/const* 'data/cons [data-level]) element head tail))
(defn- nil-of [element]
  (function/app (function/const* 'data/nil [data-level]) element))
(defn- radd [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- rat-le [l r] (function/app (function/const* 'nnrat/at-most []) l r))
(defn- eq-nnrat [l r] (function/equality type-level nnrat l r))
(defn- at-most-reflexive [v]
  (function/app (function/const* 'nnrat/at-most-reflexive []) v))
(defn- add-monotone [a a-hi b b-hi ha hb]
  (function/app (function/const* 'nnrat/add-monotone []) a a-hi b b-hi ha hb))
(defn- reflexive [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nnrat v))
(defn- map-sum [A f xs]
  (function/app (function/const* 'nnrat/map-sum [U]) A f xs))

;; nnrat/map-sum A f xs = fold (\head ih. f head + ih) 0 xs
(def map-sum-spec
  {:name 'nnrat/map-sum :kind :definition :universes ['u] :transparency :reducible
   :type (function/forall [['A type-u] ['f (function/arrow 'A nnrat)]]
                          (function/arrow (list-of 'A) nnrat))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['xs (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] nnrat)
     nnrat-zero
     (function/lam [['head 'A] ['tail (list-of 'A)] ['ih nnrat]]
                   (radd (function/app 'f 'head) 'ih))
     'xs))})

;; empty sum = 0
(def map-sum-empty-spec
  {:name 'nnrat/map-sum-empty :universes ['u]
   :type (function/forall [['A type-u] ['f (function/arrow 'A nnrat)]]
                          (eq-nnrat (map-sum 'A 'f (nil-of 'A)) nnrat-zero))
   :value (function/lam [['A type-u] ['f (function/arrow 'A nnrat)]]
                        (reflexive (map-sum 'A 'f (nil-of 'A))))})

;; cons recurrence: map-sum f (head :: tail) = f head + map-sum f tail
(def map-sum-cons-spec
  {:name 'nnrat/map-sum-cons :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)] ['head 'A] ['tail (list-of 'A)]]
          (eq-nnrat (map-sum 'A 'f (cons-of 'A 'head 'tail))
                    (radd (function/app 'f 'head) (map-sum 'A 'f 'tail))))
   :value (function/lam
           [['A type-u] ['f (function/arrow 'A nnrat)] ['head 'A] ['tail (list-of 'A)]]
           (reflexive (map-sum 'A 'f (cons-of 'A 'head 'tail))))})

;; termwise domination lifts through the finite sum
(def map-sum-monotone-spec
  {:name 'nnrat/map-sum-monotone :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
           ['hfg (function/forall [['x 'A]] (rat-le (function/app 'f 'x) (function/app 'g 'x)))]
           ['xs (list-of 'A)]]
          (rat-le (map-sum 'A 'f 'xs) (map-sum 'A 'g 'xs)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['g (function/arrow 'A nnrat)]
     ['hfg (function/forall [['x 'A]] (rat-le (function/app 'f 'x) (function/app 'g 'x)))]
     ['xs (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level zero-level])
     'A
     (function/lam [['ys (list-of 'A)]] (rat-le (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys)))
     ;; nil : map-sum f nil = 0 <= 0 = map-sum g nil
     (at-most-reflexive nnrat-zero)
     ;; cons head tail : (f head + Sf tail) <= (g head + Sg tail)
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['ih (rat-le (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail))]]
      (add-monotone (function/app 'f 'head) (function/app 'g 'head)
                    (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
                    (function/app 'hfg 'head) 'ih))
     'xs))})

(def definition-specs [map-sum-spec])
(def theorem-specs [map-sum-empty-spec map-sum-cons-spec map-sum-monotone-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.add-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-list-sum (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.list-sum))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
