(ns rainbow.algorithms.proofs.ahof.strong-wolfe
  "AHoF O15 Strong Wolfe Line Search: accept a step only when it satisfies both the
  Armijo sufficient-decrease condition and the curvature condition:

      wolfe-ok? new armijo-bound curvature curvature-bound
        = (new <= armijo-bound) AND (curvature <= curvature-bound)

  (boolean AND via logic/if-data over the two exact-rational decisions). Proved native
  and axiom-free: the two-condition acceptance with unfold, a step meeting both, and a
  step failing the curvature condition. Requires audit/decide-nnrat-at-most,
  logic/if-data (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.strong-wolfe`
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
(defn- condition [d] (function/equality type-level bool d d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- fraction [num den-pred]
  (function/app (function/const* 'nnrat/make []) (data-nat num) (data-nat den-pred)))
(defn- and-bool [a b]
  (function/app (function/const* 'logic/if-data [type-level])
                bool (condition a) a b false-value))
(defn- wolfe-ok? [new ab curv cb]
  (function/app (function/const* 'wolfe/wolfe-ok? []) new ab curv cb))

(def wolfe-ok-spec
  {:name 'wolfe/wolfe-ok? :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat bool)
   :value (function/lam [['new nnrat] ['ab nnrat] ['curv nnrat] ['cb nnrat]]
                        (and-bool (decide-at-most 'new 'ab) (decide-at-most 'curv 'cb)))})

(def definition-specs [wolfe-ok-spec])

(def wolfe-ok-unfold-spec
  {:name 'wolfe/wolfe-ok-unfold :universes []
   :type (function/forall [['new nnrat] ['ab nnrat] ['curv nnrat] ['cb nnrat]]
                          (equality bool (wolfe-ok? 'new 'ab 'curv 'cb)
                                    (and-bool (decide-at-most 'new 'ab)
                                              (decide-at-most 'curv 'cb))))
   :value (function/lam [['new nnrat] ['ab nnrat] ['curv nnrat] ['cb nnrat]]
                        (function/app (function/const* 'equality/reflexive [type-level])
                                      bool (wolfe-ok? 'new 'ab 'curv 'cb)))})

(def both-conditions-accept-spec
  {:name 'wolfe/both-conditions-accept :universes []
   :type (equality bool (wolfe-ok? (fraction 1 1) (fraction 3 3) (fraction 1 1) (fraction 3 3)) true-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (wolfe-ok? (fraction 1 1) (fraction 3 3) (fraction 1 1) (fraction 3 3)))})

(def curvature-fails-reject-spec
  {:name 'wolfe/curvature-fails-reject :universes []
   :type (equality bool (wolfe-ok? (fraction 1 1) (fraction 3 3) (fraction 3 3) (fraction 1 1)) false-value)
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        bool (wolfe-ok? (fraction 1 1) (fraction 3 3) (fraction 3 3) (fraction 1 1)))})

(def theorem-specs [wolfe-ok-unfold-spec both-conditions-accept-spec curvature-fails-reject-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-strong-wolfe
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
