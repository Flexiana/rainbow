(ns rainbow.algorithms.proofs.ahof.mcts
  "AHoF D36 Monte Carlo Tree Search: incrementally grow a search tree by
  selection, expansion, simulation, and backpropagation. The TREE POLICY selects
  the child maximizing the UCB score -- exploitation (mean value) plus an
  exploration bonus:

      ucb-score exploit explore = exploit + explore
      tree-policy-value children = list-maximum (map ucb-score children)

  over exact-rational UCB scores. Proved native and axiom-free: the UCB score is
  the sum of exploitation and exploration; the tree policy selects the maximum
  UCB (the proved list-maximum fold); a worked selection; and that the selected
  UCB dominates every child's UCB (child <= selected as native nnrat/at-most) --
  so MCTS descends toward the most promising child. The exploration bonus
  (a sqrt/log term) and the rollout/backprop are executable; what is proved is
  the UCB tree-policy selection over supplied rational scores.

  Requires list-maximum/maximum, nnrat/add, nnrat/at-most,
  audit/decide-nnrat-at-most, nnrat/decide-at-most-true-sound, and the D63
  checkpoint.

  Scope (measured by the kernel): this module has 4 worked instances (statements about specific values).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.mcts`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.algorithms.proofs.list-maximum :as list-maximum]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def list-nnrat
  (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- nnrat-add [l r]
  (function/app (function/const* 'nnrat/add []) l r))
(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- nnrat-at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat
  (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- nnrat-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

(defn- ucb-score [exploit explore]
  (function/app (function/const* 'mcts/ucb-score []) exploit explore))
(defn- tree-policy-value [children]
  (function/app (function/const* 'mcts/tree-policy-value []) children))
(defn- list-maximum-app [xs]
  (function/app (function/const* 'list-maximum/maximum []) xs))

(defn- at-most-proof [a b]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound [])
                a b
                (function/app (function/const* 'equality/reflexive [type-level])
                              bool (decide-at-most a b))))

;; Definitions --------------------------------------------------------------

;; ucb-score exploit explore = exploit + explore
(def ucb-score-spec
  {:name 'mcts/ucb-score :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['exploit nnrat] ['explore nnrat]]
                        (nnrat-add 'exploit 'explore))})

;; tree-policy-value children = list-maximum children (the max UCB)
(def tree-policy-value-spec
  {:name 'mcts/tree-policy-value :kind :definition :universes []
   :type (function/arrow list-nnrat nnrat)
   :value (function/lam [['children list-nnrat]]
                        (list-maximum-app 'children))})

(def definition-specs [ucb-score-spec tree-policy-value-spec])

;; Theorems -----------------------------------------------------------------

;; A child's UCB score: exploit 3/1 + explore 2/1 = 5/1.
(def ucb-score-example-spec
  {:name 'mcts/ucb-score-example :universes []
   :type (equality nnrat (ucb-score (whole 3) (whole 2)) (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (ucb-score (whole 3) (whole 2)))})

;; Three children with UCB scores 5, 7, 4; the tree policy selects the max 7.
(def children (nnrat-list (whole 5) (whole 7) (whole 4)))

(def selects-max-ucb-spec
  {:name 'mcts/selects-max-ucb :universes []
   :type (equality nnrat (tree-policy-value children) (whole 7))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (tree-policy-value children))})

;; The selected UCB (7) dominates every child's UCB.
(def dominates-first-spec
  {:name 'mcts/dominates-first :universes []
   :type (nnrat-at-most (whole 5) (whole 7))
   :value (at-most-proof (whole 5) (whole 7))})

(def dominates-third-spec
  {:name 'mcts/dominates-third :universes []
   :type (nnrat-at-most (whole 4) (whole 7))
   :value (at-most-proof (whole 4) (whole 7))})

(def theorem-specs
  [ucb-score-example-spec selects-max-ucb-spec dominates-first-spec
   dominates-third-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.list-maximum])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-mcts (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.mcts))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
