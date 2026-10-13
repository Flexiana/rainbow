(ns rainbow.math.nat.divisibility
  "Native natural-number divisibility for arithmetic proof interfaces.

  `nat/divides d n` is constructive evidence of a natural factor k with
  d*k = n. The definition is reducible, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.expectation :as expectation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))

(defn- app [f & xs] (apply function/app f xs))
(defn- multiply [left right]
  (app (function/const* 'nat/multiply []) left right))

(def divides-spec
  {:name 'nat/divides
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat 'Prop)
   :value
   (function/lam
    [['divisor nat] ['value nat]]
    (proposition/existence
     type-level nat
     (function/lam
      [['factor nat]]
      (function/equality
       type-level nat (multiply 'divisor 'factor) 'value))))})

(def definition-specs [divides-spec])
(def theorem-specs [])

(defn extend-environment [env]
  (let [with-multiply
        (if (environment/resolve-id env 'nat/multiply)
          env
          (support/extend-with
           env :nat-divisibility-support [expectation/nat-multiply-spec]))]
    (support/extend-with
     with-multiply :nat-divisibility definition-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
