(ns rainbow.algorithms.proofs.ahof.receding-horizon
  "AHoF D31 Receding Horizon Control (model-predictive control): rather than
  commit to a whole open-loop plan, the controller solves the finite-horizon
  problem, applies only the FIRST action of the resulting plan, then re-solves
  from the new state at the next step. The control law is the head of the plan:

      first-action default plan = head plan   (default if the plan is empty).

  Proved native and axiom-free: the first-action extraction (built by List.rec),
  its cons law (the first action of a nonempty plan is its head), and a worked
  instance. Re-solving the finite-horizon optimization each step is an executable
  concern; what is proved here is that the applied control is exactly the plan's
  first action -- the defining feature that distinguishes receding-horizon from
  open-loop control.

  Requires nnrat and data/List.rec (both in the D63 checkpoint).

  Scope (measured by the kernel): this module has 2 worked instances (statements about specific values) and 1 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.ahof.receding-horizon`
  prints this classification."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def plan-type (function/app (function/const* 'data/List [type-level]) nnrat))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- cons-nnrat [head tail]
  (function/app (function/const* 'data/cons [type-level]) nnrat head tail))
(def nil-nnrat (function/app (function/const* 'data/nil [type-level]) nnrat))

(defn- first-action [default plan]
  (function/app (function/const* 'mpc/first-action []) default plan))

;; Definitions --------------------------------------------------------------

;; first-action default plan = head plan  (default on the empty plan)
(def first-action-spec
  {:name 'mpc/first-action :kind :definition :universes []
   :type (function/arrow nnrat plan-type nnrat)
   :value
   (function/lam
    [['default nnrat] ['plan plan-type]]
    (function/app
     (function/const* 'data/List.rec [type-level type-level])
     nnrat
     (function/lam [['ignored plan-type]] nnrat)
     'default
     (function/lam [['head nnrat] ['tail plan-type] ['ignored-ih nnrat]]
                   'head)
     'plan))})

(def definition-specs [first-action-spec])

;; Theorems -----------------------------------------------------------------

(defn- data-nat [n]
  (nth (iterate #(function/app (function/const* 'data/succ []) %)
                (function/const* 'data/zero [])) n))
(defn- whole [n]
  (function/app (function/const* 'nnrat/make []) (data-nat n) (data-nat 0)))
(defn- plan-list [& elements]
  (reduce (fn [tail element] (cons-nnrat element tail)) nil-nnrat
          (reverse elements)))

;; The control law: the applied action is the plan's first action, whatever the
;; rest of the plan and the default.
(def first-action-cons-spec
  {:name 'mpc/first-action-cons :universes []
   :type (function/forall
          [['default nnrat] ['head nnrat] ['tail plan-type]]
          (equality nnrat
                    (first-action 'default (cons-nnrat 'head 'tail))
                    'head))
   :value (function/lam
           [['default nnrat] ['head nnrat] ['tail plan-type]]
           (function/app
            (function/const* 'equality/reflexive [type-level])
            nnrat (first-action 'default (cons-nnrat 'head 'tail))))})

;; Worked: the plan [5, 2, 8] applies action 5 this step (then replans).
(def first-action-example-spec
  {:name 'mpc/first-action-example :universes []
   :type (equality nnrat
                   (first-action (whole 0)
                                 (plan-list (whole 5) (whole 2) (whole 8)))
                   (whole 5))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat
                        (first-action (whole 0)
                                      (plan-list (whole 5) (whole 2)
                                                 (whole 8))))})

;; An empty plan falls back to the default (safe/idle) action.
(def first-action-empty-spec
  {:name 'mpc/first-action-empty :universes []
   :type (equality nnrat
                   (first-action (whole 0) nil-nnrat)
                   (whole 0))
   :value (function/app (function/const* 'equality/reflexive [type-level])
                        nnrat (first-action (whole 0) nil-nnrat))})

(def theorem-specs
  [first-action-cons-spec first-action-example-spec first-action-empty-spec])

;; Environment plumbing -----------------------------------------------------

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :ahof-receding-horizon (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.receding-horizon))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
