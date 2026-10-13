(ns rainbow.algorithms.proofs.ahof.ratio-normalizing
  "AHoF V31 Ratio of Normalizing Constants: estimate the ratio of two normalizing
  constants (partition functions) Z1/Z2, the quantity underlying Bayes factors and
  bridge/path sampling:

      ratio z1 z2 = z1 / z2.

  The ratio reading holds only for a POSITIVE denominator Z2 (normalizing constants are
  positive). nnrat/divide is totalised: z2 = 0 is accepted and yields a junk value (its
  reciprocal maps the equivalent zeros 0/1 and 0/2 to 1 and 2), and that zero case lies
  outside the ratio claim. Proved: ratio unfolds to nnrat/divide for all inputs (by
  reflexivity, an unfolding and not a ratio claim); with Z1 = 1/2 and Z2 = 1/4 the ratio
  is 2; equal constants 1/4, 1/4 give ratio 1. Values are proved by cross-product
  equivalence. Proved native and axiom-free. Requires nnrat/divide, nnrat/equivalent
  (all in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.ratio-normalizing`
  prints this classification."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- make-rational [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(def one-half (make-rational 1 1))
(def one-quarter (make-rational 1 3))
(def two (make-rational 2 0))
(def one (make-rational 1 0))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- multiply-nat [l r] (function/app (function/const* 'nat/multiply []) l r))
(defn- nnrat-divide [l r] (function/app (function/const* 'nnrat/divide []) l r))
(defn- nnrat-equivalent [l r] (function/app (function/const* 'nnrat/equivalent []) l r))
(defn- equivalent-cross [l r]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat (multiply-nat (numerator l) (denominator r))))
(defn- equality [carrier l r] (function/equality type-level carrier l r))

(defn- ratio [z1 z2]
  (function/app (function/const* 'ratio-nc/ratio []) z1 z2))

(def ratio-spec
  {:name 'ratio-nc/ratio :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['z1 nnrat] ['z2 nnrat]] (nnrat-divide 'z1 'z2))})

(def unequal-ratio-spec
  {:name 'ratio-nc/unequal-ratio :kind :definition :universes [] :type nnrat
   :value (ratio one-half one-quarter)})
(def equal-ratio-spec
  {:name 'ratio-nc/equal-ratio :kind :definition :universes [] :type nnrat
   :value (ratio one-quarter one-quarter)})

(def definition-specs [ratio-spec unequal-ratio-spec equal-ratio-spec])

(def ratio-unfold-spec
  {:name 'ratio-nc/ratio-unfold :universes []
   :type (function/forall [['z1 nnrat] ['z2 nnrat]]
                          (equality nnrat (ratio 'z1 'z2) (nnrat-divide 'z1 'z2)))
   :value (function/lam [['z1 nnrat] ['z2 nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      nnrat (ratio 'z1 'z2)))})

(def unequal-ratio-is-two-spec
  {:name 'ratio-nc/unequal-ratio-is-two :universes []
   :type (nnrat-equivalent (function/const* 'ratio-nc/unequal-ratio []) two)
   :value (equivalent-cross (function/const* 'ratio-nc/unequal-ratio []) two)})

(def equal-ratio-is-one-spec
  {:name 'ratio-nc/equal-ratio-is-one :universes []
   :type (nnrat-equivalent (function/const* 'ratio-nc/equal-ratio []) one)
   :value (equivalent-cross (function/const* 'ratio-nc/equal-ratio []) one)})

(def theorem-specs
  [ratio-unfold-spec unequal-ratio-is-two-spec equal-ratio-is-one-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-ratio-normalizing
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
