(ns rainbow.algorithms.proofs.ahof.shooting
  "AHoF V16 Shooting Methods: trajectory-based trajectory optimization / open-loop
  control. A candidate open-loop plan is scored by SIMULATING it -- threading the
  action sequence through the dynamics from the initial state to obtain the
  resulting state:

      simulate dynamics initial actions = fold dynamics initial actions

  where `dynamics : state -> action -> state` is the (pluggable) transition. The
  shooting method maps this simulation over a batch of candidate action sequences
  and keeps the best. Proved native and axiom-free: the simulation fold (built by
  List.rec applying the supplied two-argument dynamics), its cons recurrence, and
  a worked additive-dynamics trajectory. The candidate generation and objective
  scoring are executable concerns; what is proved here is the deterministic
  rollout.

  Requires nnrat and data/List.rec (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 1 worked instances (statements about specific values) and 2 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.shooting`
  prints this classification."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def action-list (function/app (function/const* 'data/List [type-level]) nnrat))
(def dynamics-type (function/arrow nnrat nnrat nnrat))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- simulate [dynamics initial actions]
  (function/app (function/const* 'shooting/simulate []) dynamics initial actions))

;; Definitions --------------------------------------------------------------

;; simulate dynamics initial actions = thread the actions through the dynamics.
;; (List.rec folds the actions, applying `dynamics accumulated-state action`.)
(def simulate-spec
  {:name 'shooting/simulate :kind :definition :universes []
   :type (function/arrow dynamics-type nnrat action-list nnrat)
   :value
   (function/lam
    [['dynamics dynamics-type] ['initial nnrat] ['actions action-list]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored action-list]] nnrat)
     'initial
     (function/lam [['action nnrat] ['tail action-list] ['state nnrat]]
                   (function/app 'dynamics 'state 'action))
     'actions))})

(def definition-specs [simulate-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- action-seq [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))
(def add-dynamics
  (function/lam [['state nnrat] ['action nnrat]]
                (function/app (function/const* 'nnrat/add []) 'state 'action)))

;; The rollout consumes one action: simulate over (a :: rest) applies the
;; dynamics to the head-consumed state and the head action.
(def simulate-cons-spec
  {:name 'shooting/simulate-cons :universes []
   :type (function/forall
          [['dynamics dynamics-type] ['initial nnrat]
           ['action nnrat] ['tail action-list]]
          (equality nnrat
                    (simulate 'dynamics 'initial (cons-nnrat 'action 'tail))
                    (function/app 'dynamics
                                  (simulate 'dynamics 'initial 'tail)
                                  'action)))
   :value (function/lam
           [['dynamics dynamics-type] ['initial nnrat]
            ['action nnrat] ['tail action-list]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (simulate 'dynamics 'initial (cons-nnrat 'action 'tail))))})

;; An empty plan leaves the state at the initial condition.
(def simulate-empty-spec
  {:name 'shooting/simulate-empty :universes []
   :type (function/forall
          [['dynamics dynamics-type] ['initial nnrat]]
          (equality nnrat (simulate 'dynamics 'initial nil-nnrat) 'initial))
   :value (function/lam
           [['dynamics dynamics-type] ['initial nnrat]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (simulate 'dynamics 'initial nil-nnrat)))})

;; Worked additive rollout: from state 0, applying actions 1,2,3 reaches 6.
(def simulate-example-spec
  {:name 'shooting/simulate-example :universes []
   :type (equality nnrat
                   (simulate add-dynamics (whole 0)
                             (action-seq (whole 1) (whole 2) (whole 3)))
                   (whole 6))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (simulate add-dynamics (whole 0)
                                  (action-seq (whole 1) (whole 2) (whole 3))))})

(def theorem-specs
  [simulate-cons-spec simulate-empty-spec simulate-example-spec])

;; Environment plumbing -----------------------------------------------------

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :ahof-shooting
                       (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
