(ns rainbow.math.nat.multiply-zero-split
  "nat/multiply-zero-split : a*b = 0 -> (a = 0) or (b = 0). Nested Nat.rec: a=0 gives the left
  disjunct; a=succ p with b=0 gives the right disjunct; a=succ p, b=succ q makes (succ p)*(succ q)
  a successor, so =0 is refuted. The general nat no-zero-divisors -- foundation for the general
  nnrat/signed no-zero-divisors that strict convexity needs (generalizes nat/square-zero-implies-zero)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.nat.semiring :as nat-semiring]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private prop-lvl [:zero])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refln [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- eq-symm [x y h] (app (function/const* 'equality/symmetric [ulvl]) nat x y h))
(defn- zero-not-succ [v] (app (function/const* 'nat/zero-not-successor []) v))
(defn- explode [result imp] (app (function/const* 'proposition/explode []) result imp))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))

(def multiply-zero-split-spec
  {:name 'nat/multiply-zero-split
   :universes []
   :type (function/forall [['a nat] ['b nat] ['h (eqn (nmul 'a 'b) zero)]]
                          (disjt (eqn 'a zero) (eqn 'b zero)))
   :value
   (function/lam
    [['a nat] ['b nat] ['h (eqn (nmul 'a 'b) zero)]]
    (app (function/app
          (function/const* 'data/Nat.rec [prop-lvl])
          ;; motive on a: av |-> (av*b = 0) -> ((av=0) or (b=0))
          (function/lam [['av nat]]
                        (function/arrow (eqn (nmul 'av 'b) zero)
                                        (disjt (eqn 'av zero) (eqn 'b zero))))
          ;; base a=0: 0*b defeq 0; conclude left disjunct 0=0
          (function/lam [['h0 (eqn (nmul zero 'b) zero)]]
                        (left-disj (eqn zero zero) (eqn 'b zero) (refln zero)))
          ;; step a=succ p: inner Nat.rec on b
          (function/lam
           [['p nat] ['ih (function/arrow (eqn (nmul 'p 'b) zero)
                                          (disjt (eqn 'p zero) (eqn 'b zero)))]]
           (function/app
            (function/app
             (function/const* 'data/Nat.rec [prop-lvl])
             ;; motive on b: bv |-> ((succ p)*bv = 0) -> ((succ p = 0) or (bv = 0))
             (function/lam [['bv nat]]
                           (function/arrow (eqn (nmul (succ 'p) 'bv) zero)
                                           (disjt (eqn (succ 'p) zero) (eqn 'bv zero))))
             ;; inner base b=0: conclude right disjunct 0=0
             (function/lam [['hb0 (eqn (nmul (succ 'p) zero) zero)]]
                           (right-disj (eqn (succ 'p) zero) (eqn zero zero) (refln zero)))
             ;; inner step b=succ q: (succ p)*(succ q) = succ(q + p*(succ q)); refute succ=0
             (function/lam
              [['q nat] ['ihb (function/arrow (eqn (nmul (succ 'p) 'q) zero)
                                              (disjt (eqn (succ 'p) zero) (eqn 'q zero)))]]
              (function/lam
               [['hbs (eqn (nmul (succ 'p) (succ 'q)) zero)]]
               (explode (disjt (eqn (succ 'p) zero) (eqn (succ 'q) zero))
                        (app (zero-not-succ (nadd 'q (nmul 'p (succ 'q))))
                             (eq-symm (nmul (succ 'p) (succ 'q)) zero 'hbs))))))
            'b))
          'a)
         'h))})

(def theorem-specs [multiply-zero-split-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.infinite rainbow.math.nat.semiring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-multiply-zero-split theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.multiply-zero-split))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
