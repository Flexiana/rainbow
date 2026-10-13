(ns rainbow.algorithms.proofs.ahof.direct
  "AHoF O37 DIRECT (DIvided RECTangles): a Lipschitzian global optimizer that
  partitions the domain into rectangles and subdivides the 'potentially optimal' ones.
  Among rectangles of comparable size the more promising one has the smaller center
  value, so the selection core is the minimum of two center values:

      prefers-lower?  a b = decide (a <= b)
      more-promising  a b = if (a <= b) then a else b   (the smaller center value)

  over exact rationals. Proved native and axiom-free: the preference decision, the
  more-promising (min) selection in both orders, and a worked preference. Requires
  audit/decide-nnrat-at-most, logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 3 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.direct`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- condition [decision]
  (function/equality type-level bool decision decision))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))

(defn- prefers-lower? [a b]
  (function/app (function/const* 'direct-opt/prefers-lower? []) a b))
(defn- more-promising [a b]
  (function/app (function/const* 'direct-opt/more-promising []) a b))

(def prefers-lower-spec
  {:name 'direct-opt/prefers-lower? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['a nnrat] ['b nnrat]] (decide-at-most 'a 'b))})

(def more-promising-spec
  {:name 'direct-opt/more-promising :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (function/app (function/const* 'logic/if-data [type-level])
                                      nnrat (condition (decide-at-most 'a 'b))
                                      (decide-at-most 'a 'b) 'a 'b))})

(def definition-specs [prefers-lower-spec more-promising-spec])

;; The more promising of center values 1/2 and 3/4 is 1/2.
(def selects-lower-center-spec
  {:name 'direct-opt/selects-lower-center :universes []
   :type (equality nnrat (more-promising (fraction 1 1) (fraction 3 3)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (more-promising (fraction 1 1) (fraction 3 3)))})

;; ...and the same with the rectangles swapped.
(def selects-lower-center-symmetric-spec
  {:name 'direct-opt/selects-lower-center-symmetric :universes []
   :type (equality nnrat (more-promising (fraction 3 3) (fraction 1 1)) (fraction 1 1))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (more-promising (fraction 3 3) (fraction 1 1)))})

;; The lower center value 1/2 is preferred over 3/4.
(def prefers-lower-example-spec
  {:name 'direct-opt/prefers-lower-example :universes []
   :type (equality bool (prefers-lower? (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (prefers-lower? (fraction 1 1) (fraction 3 3)))})

(def theorem-specs
  [selects-lower-center-spec selects-lower-center-symmetric-spec
   prefers-lower-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-direct (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.direct))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
