(ns rainbow.math.rational.signed.list-sum
  "Finite sums of signed rationals over a list, and their order laws.

    signed/map-sum A f xs      = f x0 + f x1 + ... + f xn   (empty sum = 0)
    signed/map-sum-monotone    : (forall x, f x <= g x) -> sum f xs <= sum g xs
    signed/map-sum-nonpositive : (forall x, f x <= 0)    -> sum f xs <= 0
    signed/map-sum-nonnegative : (forall x, 0 <= f x)    -> 0 <= sum f xs

  The nnrat side already had `nnrat/map-sum`; the signed side had nothing, so
  every aggregate over signed quantities -- a Lagrangian penalty, a dot product,
  a total reward with sign -- had to stay abstract.  These are the same List.rec
  folds: nil is order-reflexivity at `signed/zero`, cons is `signed/add-monotone`
  against the induction hypothesis, and the two sign versions additionally
  collapse the `0 + 0` produced in the cons step with `signed/add-zero-right`.

  Polymorphic in the index type.  Native and axiom-free; chains signed order
  monotonicity and signed limit uniqueness (for signed/add-zero-right) on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.order-monotone :as monotone]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- list-of [element]
  (app (function/const* 'data/List [data-level]) element))
(defn- cons-of [element head tail]
  (app (function/const* 'data/cons [data-level]) element head tail))
(defn- nil-of [element]
  (app (function/const* 'data/nil [data-level]) element))
(defn- sadd [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- eq-signed [a b] (function/equality type-level signed a b))
(defn- map-sum [A f xs] (app (function/const* 'signed/map-sum [U]) A f xs))

(defn- signed-refl-eq [v]
  (app (function/const* 'equality/reflexive [type-level]) signed v))
(defn- signed-at-most-reflexive [v]
  (app (function/const* 'signed/at-most-reflexive []) v))
(defn- signed-equiv-reflexive [v]
  (app (function/const* 'signed/equivalent-reflexive []) v))
(defn- signed-add-monotone [a ah b bh ha hb]
  (app (function/const* 'signed/add-monotone []) a ah b bh ha hb))
(defn- signed-add-zero-right [v]
  (app (function/const* 'signed/add-zero-right []) v))
(defn- signed-at-most-respects [a ah b bh same-a same-b ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       a ah b bh same-a same-b ordered))

(def zero-plus-zero (sadd signed-zero signed-zero))

;; signed/map-sum A f xs = fold (\head ih. f head + ih) 0 xs
(def map-sum-spec
  {:name 'signed/map-sum :kind :definition :universes ['u]
   :transparency :reducible
   :type (function/forall [['A type-u] ['f (function/arrow 'A signed)]]
                          (function/arrow (list-of 'A) signed))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A signed)] ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level type-level])
         'A
         (function/lam [['ignored (list-of 'A)]] signed)
         signed-zero
         (function/lam [['head 'A] ['tail (list-of 'A)] ['ih signed]]
                       (sadd (app 'f 'head) 'ih))
         'xs))})

(def map-sum-empty-spec
  {:name 'signed/map-sum-empty :universes ['u]
   :type (function/forall [['A type-u] ['f (function/arrow 'A signed)]]
                          (eq-signed (map-sum 'A 'f (nil-of 'A)) signed-zero))
   :value (function/lam [['A type-u] ['f (function/arrow 'A signed)]]
                        (signed-refl-eq (map-sum 'A 'f (nil-of 'A))))})

(def map-sum-cons-spec
  {:name 'signed/map-sum-cons :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A signed)]
           ['head 'A] ['tail (list-of 'A)]]
          (eq-signed (map-sum 'A 'f (cons-of 'A 'head 'tail))
                     (sadd (app 'f 'head) (map-sum 'A 'f 'tail))))
   :value (function/lam
           [['A type-u] ['f (function/arrow 'A signed)]
            ['head 'A] ['tail (list-of 'A)]]
           (signed-refl-eq (map-sum 'A 'f (cons-of 'A 'head 'tail))))})

(def map-sum-monotone-spec
  {:name 'signed/map-sum-monotone :universes ['u]
   :type (function/forall
          [['A type-u]
           ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
           ['hfg (function/forall [['x 'A]] (sle (app 'f 'x) (app 'g 'x)))]
           ['xs (list-of 'A)]]
          (sle (map-sum 'A 'f 'xs) (map-sum 'A 'g 'xs)))
   :value
   (function/lam
    [['A type-u]
     ['f (function/arrow 'A signed)] ['g (function/arrow 'A signed)]
     ['hfg (function/forall [['x 'A]] (sle (app 'f 'x) (app 'g 'x)))]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam [['ys (list-of 'A)]]
                       (sle (map-sum 'A 'f 'ys) (map-sum 'A 'g 'ys)))
         (signed-at-most-reflexive signed-zero)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (sle (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail))]]
          (signed-add-monotone (app 'f 'head) (app 'g 'head)
                               (map-sum 'A 'f 'tail) (map-sum 'A 'g 'tail)
                               (app 'hfg 'head) 'ih))
         'xs))})

;; A sum of nonpositive terms is nonpositive.  The cons step lands on 0 + 0,
;; which add-zero-right collapses back to 0.
(def map-sum-nonpositive-spec
  {:name 'signed/map-sum-nonpositive :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A signed)]
           ['hf (function/forall [['x 'A]] (sle (app 'f 'x) signed-zero))]
           ['xs (list-of 'A)]]
          (sle (map-sum 'A 'f 'xs) signed-zero))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A signed)]
     ['hf (function/forall [['x 'A]] (sle (app 'f 'x) signed-zero))]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam [['ys (list-of 'A)]]
                       (sle (map-sum 'A 'f 'ys) signed-zero))
         (signed-at-most-reflexive signed-zero)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (sle (map-sum 'A 'f 'tail) signed-zero)]]
          (let [total (sadd (app 'f 'head) (map-sum 'A 'f 'tail))]
            (signed-at-most-respects
             total total zero-plus-zero signed-zero
             (signed-equiv-reflexive total)
             (signed-add-zero-right signed-zero)
             (signed-add-monotone (app 'f 'head) signed-zero
                                  (map-sum 'A 'f 'tail) signed-zero
                                  (app 'hf 'head) 'ih))))
         'xs))})

;; ... and dually.
(def map-sum-nonnegative-spec
  {:name 'signed/map-sum-nonnegative :universes ['u]
   :type (function/forall
          [['A type-u] ['f (function/arrow 'A signed)]
           ['hf (function/forall [['x 'A]] (sle signed-zero (app 'f 'x)))]
           ['xs (list-of 'A)]]
          (sle signed-zero (map-sum 'A 'f 'xs)))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A signed)]
     ['hf (function/forall [['x 'A]] (sle signed-zero (app 'f 'x)))]
     ['xs (list-of 'A)]]
    (app (function/const* 'data/List.rec [data-level zero-level])
         'A
         (function/lam [['ys (list-of 'A)]]
                       (sle signed-zero (map-sum 'A 'f 'ys)))
         (signed-at-most-reflexive signed-zero)
         (function/lam
          [['head 'A] ['tail (list-of 'A)]
           ['ih (sle signed-zero (map-sum 'A 'f 'tail))]]
          (let [total (sadd (app 'f 'head) (map-sum 'A 'f 'tail))]
            (signed-at-most-respects
             zero-plus-zero signed-zero total total
             (signed-add-zero-right signed-zero)
             (signed-equiv-reflexive total)
             (signed-add-monotone signed-zero (app 'f 'head)
                                  signed-zero (map-sum 'A 'f 'tail)
                                  (app 'hf 'head) 'ih))))
         'xs))})

(def definition-specs [map-sum-spec])
(def theorem-specs
  [map-sum-empty-spec map-sum-cons-spec map-sum-monotone-spec
   map-sum-nonpositive-spec map-sum-nonnegative-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniqueness/extend-environment
      monotone/extend-environment
      (support/extend-with :signed-list-sum
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
