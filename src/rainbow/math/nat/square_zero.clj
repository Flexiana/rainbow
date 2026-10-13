(ns rainbow.math.nat.square-zero
  "nat/square-zero-implies-zero : a*a = 0 -> a = 0. Nat.rec on a: base 0 is reflexivity; the
  successor case makes a*a a successor, so a*a=0 is succ(..)=0, refuted by zero-not-successor.
  Sub-brick (1) of the nnrat AM-GM discriminant for signed no-zero-divisors."
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

(def square-zero-implies-zero-spec
  {:name 'nat/square-zero-implies-zero
   :universes []
   :type (function/forall [['a nat] ['h (eqn (nmul 'a 'a) zero)]] (eqn 'a zero))
   :value
   (function/lam
    [['a nat] ['h (eqn (nmul 'a 'a) zero)]]
    (app (function/app
          (function/const* 'data/Nat.rec [prop-lvl])
          ;; motive: a |-> (a*a = 0) -> (a = 0)
          (function/lam [['av nat]] (function/arrow (eqn (nmul 'av 'av) zero) (eqn 'av zero)))
          ;; base a=0: 0*0=0 defeq, goal 0=0
          (function/lam [['h0 (eqn (nmul zero zero) zero)]] (refln zero))
          ;; step a=succ p: (succ p)*(succ p) = succ(p + p*(succ p)); succ(..)=0 is impossible
          (function/lam
           [['p nat] ['ih (function/arrow (eqn (nmul 'p 'p) zero) (eqn 'p zero))]]
           (function/lam
            [['hs (eqn (nmul (succ 'p) (succ 'p)) zero)]]
            (explode (eqn (succ 'p) zero)
                     (app (zero-not-succ (nadd 'p (nmul 'p (succ 'p))))
                          (eq-symm (nmul (succ 'p) (succ 'p)) zero 'hs)))))
          'a)
         'h))})

(def theorem-specs [square-zero-implies-zero-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.infinite rainbow.math.nat.semiring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-square-zero theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.square-zero))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
