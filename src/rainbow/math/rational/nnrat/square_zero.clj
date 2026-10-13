(ns rainbow.math.rational.nnrat.square-zero
  "nnrat/square-zero : m*m ~ 0 -> m ~ 0. Sub-brick (2) of the AM-GM. nnrat-equivalent a zero
  unfolds to a nat equality (num a)*(den zero) = 0 with den zero = succ zero, so it is (num a)*1;
  strip the *1 (multiply-one-right), apply nat/square-zero-implies-zero to (num m)^2, then rebuild
  m ~ 0 by substituting num m = 0."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.square-zero :as nat-sq]
            [rainbow.math.nat.semiring :as nat-semiring]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- num [m] (app (function/const* 'nnrat/numerator []) m))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- mult [a b] (app (function/const* 'nnrat/multiply []) a b))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- nnequiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refln [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- eq-symm [x y h] (app (function/const* 'equality/symmetric [ulvl]) nat x y h))
(defn- eq-trans [x y z h1 h2] (app (function/const* 'equality/transitive [ulvl]) nat x y z h1 h2))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- mult-one-right [x] (app (function/const* 'nat/multiply-one-right []) x))
(defn- nat-square-zero [a h] (app (function/const* 'nat/square-zero-implies-zero []) a h))

(def square-zero-spec
  {:name 'nnrat/square-zero
   :universes []
   :type (function/forall [['m nnrat] ['h (nnequiv (mult 'm 'm) nnzero)]]
                          (nnequiv 'm nnzero))
   :value
   (function/lam
    [['m nnrat] ['h (nnequiv (mult 'm 'm) nnzero)]]
    ;; h :defeq eqn (nmul (num m * num m) (succ zero)) zero
    (let [nm (num 'm)
          X (nmul nm nm)
          xsz (nmul X (succ zero))
          m1 (mult-one-right X)                                   ; eqn xsz X
          numsq0 (eq-trans X xsz zero (eq-symm xsz X m1) 'h)      ; eqn X zero
          numm0 (nat-square-zero nm numsq0)                       ; eqn nm zero
          P (function/lam [['t nat]] (eqn (nmul 't (succ zero)) zero))]
      ;; transport P zero (= eqn (0*1) 0 = refl) to P (num m) = eqn (num m * 1) 0 = (m ~ 0)
      (subst zero nm (eq-symm nm zero numm0) P (refln zero))))})

(def theorem-specs [square-zero-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.square-zero rainbow.math.nat.semiring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-square-zero theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.square-zero))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
