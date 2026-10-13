(ns rainbow.math.rational.signed.lp-objective-negate
  "Generic finite-sum negation and formal LP minimization sense transport.
  Covers arbitrary carriers and finite lists, including empty/repeated indices.
  Does not identify a host mapv-negation with the formal mapping without evidence."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.map-sum-algebra :as sums]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.rational.signed.negate-additive :as additive]
            [rainbow.math.linear.vector.dot-negate :as scalar]
            [rainbow.math.rational.signed.deviation-rows :as order]
            [rainbow.math.rational.signed.order-respects :as respects]))

(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def signed (f/const* 'signed/SignedRational []))
(def zero (f/const* 'signed/zero []))
(defn- app [name & args] (apply f/app (f/const* name []) args))
(defn- poly [name & args] (apply f/app (f/const* name [U]) args))
(defn- list-of [A] (f/app (f/const* 'data/List [data-level]) A))
(defn- neg [x] (app 'signed/negate x))
(defn- eqv [x y] (app 'signed/equivalent x y))
(defn- le [x y] (app 'signed/at-most x y))
(defn- sum [A m xs] (poly 'signed/map-sum A m xs))
(defn- negative-map [A m] (f/lam [['i A]] (neg (f/app m 'i))))
(defn- products [A c x]
  (f/lam [['i A]] (app 'signed/multiply (f/app c 'i) (f/app x 'i))))
(defn- trans [a b c ab bc] (app 'signed/equivalent-transitive a b c ab bc))
(defn- sym [a b ab] (app 'signed/equivalent-symmetric a b ab))

(def map-sum-negate-spec
  {:name 'signed/map-sum-negate :universes ['u]
   :type (f/forall [['A type-u] ['m (f/arrow 'A signed)] ['xs (list-of 'A)]]
                   (eqv (sum 'A (negative-map 'A 'm) 'xs) (neg (sum 'A 'm 'xs))))
   :value
   (f/lam
    [['A type-u] ['m (f/arrow 'A signed)] ['xs (list-of 'A)]]
    (let [nm (negative-map 'A 'm)]
      (f/app
       (f/const* 'data/List.rec [data-level [:zero]]) 'A
       (f/lam [['ys (list-of 'A)]] (eqv (sum 'A nm 'ys) (neg (sum 'A 'm 'ys))))
       (sym (neg zero) zero (f/const* 'signed/negate-zero []))
       (f/lam
        [['h 'A] ['t (list-of 'A)] ['ih (eqv (sum 'A nm 't) (neg (sum 'A 'm 't)))]]
        (let [head (f/app 'm 'h) tail (sum 'A 'm 't)
              ntail (sum 'A nm 't)
              start (app 'signed/add (neg head) ntail)
              middle (app 'signed/add (neg head) (neg tail))
              finish (neg (app 'signed/add head tail))]
          (trans start middle finish
                 (app 'signed/add-respects-equivalence (neg head) (neg head) ntail (neg tail)
                      (app 'signed/equivalent-reflexive (neg head)) 'ih)
                 (sym finish middle (app 'signed/negate-additive head tail)))))
       'xs)))})

(def lp-objective-negate-spec
  {:name 'signed/lp-objective-negate :universes ['u]
   :type
   (f/forall [['A type-u] ['c (f/arrow 'A signed)] ['x (f/arrow 'A signed)] ['xs (list-of 'A)]]
             (eqv (sum 'A (products 'A (negative-map 'A 'c) 'x) 'xs)
                  (neg (sum 'A (products 'A 'c 'x) 'xs))))
   :value
   (f/lam
    [['A type-u] ['c (f/arrow 'A signed)] ['x (f/arrow 'A signed)] ['xs (list-of 'A)]]
    (let [p (products 'A 'c 'x) np (negative-map 'A p)
          changed (products 'A (negative-map 'A 'c) 'x)]
      (trans
       (sum 'A changed 'xs) (sum 'A np 'xs) (neg (sum 'A p 'xs))
       (poly 'signed/map-sum-respects-equivalence 'A changed np
             (f/lam [['i 'A]] (app 'signed/multiply-negate-left (f/app 'c 'i) (f/app 'x 'i))) 'xs)
       (poly 'signed/map-sum-negate 'A p 'xs))))})

(def negated-objective-bound-to-lower-spec
  (let [bindings [['A type-u] ['c (f/arrow 'A signed)] ['x (f/arrow 'A signed)]
                  ['xs (list-of 'A)] ['lower signed]]
        obj (sum 'A (products 'A 'c 'x) 'xs)
        neg-obj (sum 'A (products 'A (negative-map 'A 'c) 'x) 'xs)
        bindings (conj bindings ['ordered (le neg-obj (neg 'lower))])]
    {:name 'signed/lp-negated-objective-bound-to-lower :universes ['u]
     :type (f/forall bindings (le 'lower obj))
     :value
     (f/lam
      bindings
      (let [negative-order
            (app 'signed/at-most-respects-equivalence neg-obj (neg obj) (neg 'lower) (neg 'lower)
                 (poly 'signed/lp-objective-negate 'A 'c 'x 'xs)
                 (app 'signed/equivalent-reflexive (neg 'lower)) 'ordered)
            reversed (app 'signed/negate-reverses-order (neg obj) (neg 'lower) negative-order)]
        (app 'signed/at-most-respects-equivalence
             (neg (neg 'lower)) 'lower (neg (neg obj)) obj
             (app 'signed/negate-involutive 'lower)
             (app 'signed/negate-involutive obj) reversed)))}))

(def theorem-specs [map-sum-negate-spec lp-objective-negate-spec negated-objective-bound-to-lower-spec])
(defn extend-environment [env]
  (-> env sums/extend-environment ring/extend-environment equivalence/extend-environment
      additive/extend-environment order/extend-environment respects/extend-environment
      (support/add-spec-shared :vector-dot-negate scalar/negate-zero-spec)
      (support/add-spec-shared :vector-dot-negate scalar/multiply-negate-left-spec)
      (support/extend-with :signed-lp-objective-negate theorem-specs)))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
