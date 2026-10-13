(ns rainbow.math.nat.multiply-positive
  "Constructive nat positivity of a product: 0 < a -> 0 < b -> 0 < a*b (strict-below form).
  Bottom brick of the magnitude route to signed no-zero-divisors. strict-below 0 X unfolds to
  exists extra, succ(0)+extra = X; the proof CPS-eliminates the two witnesses, transports a*b
  along a=succ(0)+ea and the inner b=succ(0)+eb (equality/substitution), landing on
  succ(eb + ea*b), which is positive by a direct witness."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.infinite :as nat-infinite]
            [rainbow.math.nat.semiring :as nat-semiring]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- sbelow [a b] (app (function/const* 'nat/strict-below []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refln [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- ex-witness [P v ev] (app (function/const* 'proposition/witness [ulvl]) nat P v ev))

;; 0 < succ X, directly
(defn- positive-succ [X]
  (ex-witness (function/lam [['extra nat]] (eqn (nadd (succ zero) 'extra) (succ X)))
              X (refln (succ X))))

(def multiply-positive-spec
  {:name 'nat/multiply-positive
   :universes []
   :type (function/forall [['a nat] ['b nat]
                           ['ha (sbelow zero 'a)] ['hb (sbelow zero 'b)]]
                          (sbelow zero (nmul 'a 'b)))
   :value
   (function/lam
    [['a nat] ['b nat] ['ha (sbelow zero 'a)] ['hb (sbelow zero 'b)]]
    (app 'ha (sbelow zero (nmul 'a 'b))
         (function/lam
          [['ea nat] ['eea (eqn (nadd (succ zero) 'ea) 'a)]]
          (app 'hb (sbelow zero (nmul 'a 'b))
               (function/lam
                [['eb nat] ['eeb (eqn (nadd (succ zero) 'eb) 'b)]]
                ;; transport a -> succ(0)+ea in (t*b), inner needs 0 < (succ(0)+ea)*b ~ b + ea*b
                (subst (nadd (succ zero) 'ea) 'a 'eea
                       (function/lam [['t nat]] (sbelow zero (nmul 't 'b)))
                       ;; transport first b -> succ(0)+eb in (t + ea*b)
                       (subst (nadd (succ zero) 'eb) 'b 'eeb
                              (function/lam [['t nat]] (sbelow zero (nadd 't (nmul 'ea 'b))))
                              ;; 0 < succ(eb + ea*b), defeq to the transported goals
                              (positive-succ (nadd 'eb (nmul 'ea 'b))))))))))})

(def theorem-specs [multiply-positive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.infinite rainbow.math.nat.semiring])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-multiply-positive theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.multiply-positive))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
