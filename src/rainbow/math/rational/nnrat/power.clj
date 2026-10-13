(ns rainbow.math.rational.nnrat.power
  "Exact powers of a nonnegative rational.

  `nnrat/power base steps` is the Nat recursor over multiplication from
  one, so `power base 0` reduces to one and `power base (succ n)` reduces
  to `base * power base n` definitionally -- consumers rewrite by
  reflexivity, no unfold lemmas needed. Built for the geometric decay of
  total variation along kernel iterates; generic and reusable anywhere an
  exact rational envelope is stated. Native on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))

(def power-spec
  {:name 'nnrat/power :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow nnrat nat nnrat)
   :value
   (function/lam
    [['base nnrat] ['steps nat]]
    (app (function/const* 'data/Nat.rec [type-level])
         (function/lam [['ignored nat]] nnrat)
         nnrat-one
         (function/lam
          [['previous-step nat] ['accumulated nnrat]]
          (app (function/const* 'nnrat/multiply []) 'base 'accumulated))
         'steps))})

(def definition-specs [power-spec])
(def theorem-specs [])

(defn extend-environment [env]
  (support/extend-with env :nnrat-power definition-specs))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
