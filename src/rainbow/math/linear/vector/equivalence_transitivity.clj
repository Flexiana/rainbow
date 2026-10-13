(ns rainbow.math.linear.vector.equivalence-transitivity
  "Transitivity of length-sensitive componentwise vector equivalence.

  Each vector equivalence yields pointwise bounds in both directions.  Compose
  the forward bounds and the backward bounds with vector/at-most-transitive,
  then recover vector equivalence by vector/at-most-antisymmetric.  This avoids
  duplicating the underlying two-list induction."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def equivalent-transitive-spec
  {:name 'vector/equivalent-transitive :universes []
   :type
   (function/forall
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (vector-equivalent 'left 'middle)]
     ['middle-right (vector-equivalent 'middle 'right)]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['middle vector-type] ['right vector-type]
     ['left-middle (vector-equivalent 'left 'middle)]
     ['middle-right (vector-equivalent 'middle 'right)]]
    (let [left-middle-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               'left 'middle 'left-middle)
          middle-right-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               'middle 'right 'middle-right)
          left-middle-forward
          (proposition-left
           (vector-at-most 'left 'middle)
           (vector-at-most 'middle 'left)
           left-middle-bounds)
          middle-left-backward
          (proposition-right
           (vector-at-most 'left 'middle)
           (vector-at-most 'middle 'left)
           left-middle-bounds)
          middle-right-forward
          (proposition-left
           (vector-at-most 'middle 'right)
           (vector-at-most 'right 'middle)
           middle-right-bounds)
          right-middle-backward
          (proposition-right
           (vector-at-most 'middle 'right)
           (vector-at-most 'right 'middle)
           middle-right-bounds)
          left-right
          (app (function/const* 'vector/at-most-transitive [])
               'left 'middle 'right
               left-middle-forward middle-right-forward)
          right-left
          (app (function/const* 'vector/at-most-transitive [])
               'right 'middle 'left
               right-middle-backward middle-left-backward)]
      (app (function/const* 'vector/at-most-antisymmetric [])
           'left 'right left-right right-left)))})

(def definition-specs [])
(def theorem-specs [equivalent-transitive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.pointwise-order-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-equivalence-transitivity theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.equivalence-transitivity))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
