(ns rainbow.algorithms.proofs.ahof.astar
  "AHoF D37 A* / heuristic search: the priority by which A* expands nodes is the
  estimated total cost through a node, the path cost so far plus the heuristic
  estimate of the cost to go:

      f g h = g + h

  over exact-rational costs. A* pops the frontier node of least f. Proved native
  and axiom-free: the f-value is the sum, and the admissibility bound -- when the
  heuristic h underestimates the true remaining cost c (h <= c), the priority
  underestimates the true total path cost (f g h <= g + c), which is exactly what
  guarantees A* returns an optimal path. The frontier, the expansion, and the
  successor generation are executable concerns; what is proved here is the
  f-value and the admissibility bound.

  Requires nnrat/add, nnrat/at-most, and the decidable nnrat order (D63).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.astar`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- nnrat-add [l r] (function/app (function/const* 'nnrat/add []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- f-value [g h] (function/app (function/const* 'astar/f-value []) g h))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; f g h = g + h  (path cost so far plus heuristic estimate to go)
(def f-value-spec
  {:name 'astar/f-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['g nnrat] ['h nnrat]] (nnrat-add 'g 'h))})

(def definition-specs [f-value-spec])

;; Theorems -----------------------------------------------------------------

(def f-value-unfold-spec
  {:name 'astar/f-value-unfold :universes []
   :type (function/forall
          [['g nnrat] ['h nnrat]]
          (equality nnrat (f-value 'g 'h) (nnrat-add 'g 'h)))
   :value (function/lam [['g nnrat] ['h nnrat]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         nnrat (f-value 'g 'h)))})

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))

;; Worked priority: path cost 3, heuristic 4 -> f = 7.
(def f-value-example-spec
  {:name 'astar/f-value-example :universes []
   :type (equality nnrat (f-value (whole 3) (whole 4)) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (f-value (whole 3) (whole 4)))})

;; Admissibility: an underestimating heuristic (h = 4 <= true remaining cost
;; c = 5) makes the priority underestimate the true total (f 3 4 <= 3 + 5),
;; so A* never overlooks an optimal path.
(def admissibility-bound-spec
  {:name 'astar/admissibility-bound :universes []
   :type (nnrat-at-most (f-value (whole 3) (whole 4))
                        (nnrat-add (whole 3) (whole 5)))
   :value (at-most-proof (f-value (whole 3) (whole 4))
                         (nnrat-add (whole 3) (whole 5)))})

(def theorem-specs
  [f-value-unfold-spec f-value-example-spec admissibility-bound-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-astar (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.astar))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
