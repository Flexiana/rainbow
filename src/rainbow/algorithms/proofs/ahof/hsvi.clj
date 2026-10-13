(ns rainbow.algorithms.proofs.ahof.hsvi
  "AHoF D73 HSVI (Heuristic Search Value Iteration for POMDPs): maintain an upper and
  a lower bound on the optimal value function and search belief points to tighten
  them; the algorithm has converged at a belief when the bound gap is within the
  target precision:

      converged? gap epsilon = decide (gap <= epsilon).

  A gap 1/4 within precision 1/2 is converged; a gap exactly at precision is
  converged; a gap 3/4 above precision is not. Proved native and axiom-free
  (decision, converged and boundary instances, at-most gap certificate, unconverged).
  Requires audit/decide-nnrat-at-most, nnrat/at-most, nnrat/decide-at-most-true-sound.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.hsvi`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- converged? [gap epsilon]
  (function/app (function/const* 'hsvi/converged? []) gap epsilon))
(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

(def converged-spec
  {:name 'hsvi/converged? :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['gap nnrat] ['epsilon nnrat]] (decide-at-most 'gap 'epsilon))})

(def definition-specs [converged-spec])

(def small-gap-converged-spec
  {:name 'hsvi/small-gap-converged :universes []
   :type (equality bool (converged? (fraction 1 3) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (converged? (fraction 1 3) (fraction 1 1)))})

(def boundary-gap-converged-spec
  {:name 'hsvi/boundary-gap-converged :universes []
   :type (equality bool (converged? (fraction 1 1) (fraction 1 1)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (converged? (fraction 1 1) (fraction 1 1)))})

(def gap-certificate-spec
  {:name 'hsvi/gap-certificate :universes []
   :type (nnrat-at-most (fraction 1 3) (fraction 1 1))
   :value (at-most-proof (fraction 1 3) (fraction 1 1))})

(def large-gap-unconverged-spec
  {:name 'hsvi/large-gap-unconverged :universes []
   :type (equality bool (converged? (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (converged? (fraction 3 3) (fraction 1 1)))})

(def theorem-specs
  [small-gap-converged-spec boundary-gap-converged-spec gap-certificate-spec
   large-gap-unconverged-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-hsvi
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
