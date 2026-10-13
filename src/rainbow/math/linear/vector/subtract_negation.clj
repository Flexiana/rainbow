(ns rainbow.math.linear.vector.subtract-negation
  "Interaction laws between native vector subtraction and negation.

    left - (-right)  ~  left + right
    -(left - right)  ~  right - left

  The proofs normalize subtraction to addition of a negation and compose vector
  congruence, negation involutivity, negation distributivity, commutativity, and
  equivalence transitivity.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.negate-additive :as signed-additive]
            [rainbow.math.linear.vector.equivalence-transitivity :as transitivity]
            [rainbow.math.linear.vector.negate-additive :as negate-additive]
            [rainbow.math.linear.vector.subtract-laws :as subtract-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))

(def subtract-negate-spec
  {:name 'vector/subtract-negate :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-subtract 'left (vector-negate 'right))
     (vector-add 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (app
     (function/const* 'vector/add-respects-equivalence [])
     'left 'left
     (vector-negate (vector-negate 'right)) 'right
     (app (function/const* 'vector/equivalent-reflexive []) 'left)
     (app (function/const* 'vector/negate-involutive []) 'right)))})

(def negate-subtract-spec
  {:name 'vector/negate-subtract :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-negate (vector-subtract 'left 'right))
     (vector-subtract 'right 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [start (vector-negate (vector-subtract 'left 'right))
          distributed
          (vector-add
           (vector-negate 'left)
           (vector-negate (vector-negate 'right)))
          reduced
          (vector-add (vector-negate 'left) 'right)
          finish (vector-subtract 'right 'left)
          distribute
          (app (function/const* 'vector/negate-additive [])
               'left (vector-negate 'right))
          eliminate-double-negation
          (app
           (function/const* 'vector/add-respects-equivalence [])
           (vector-negate 'left) (vector-negate 'left)
           (vector-negate (vector-negate 'right)) 'right
           (app (function/const* 'vector/equivalent-reflexive [])
                (vector-negate 'left))
           (app (function/const* 'vector/negate-involutive []) 'right))
          commute
          (app (function/const* 'vector/add-commutative [])
               (vector-negate 'left) 'right)]
      (app
       (function/const* 'vector/equivalent-transitive [])
       start reduced finish
       (app (function/const* 'vector/equivalent-transitive [])
            start distributed reduced
            distribute eliminate-double-negation)
       commute)))})

(def definition-specs [])
(def theorem-specs [subtract-negate-spec negate-subtract-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.subtract-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/negate-additive :signed-negate-additive signed-additive/negate-additive-spec) (extend-spec-if-missing 'vector/negate-additive :vector-negate-additive negate-additive/negate-additive-spec) (extend-spec-if-missing 'vector/equivalent-transitive :vector-equivalence-transitivity transitivity/equivalent-transitive-spec) (support/extend-with :vector-subtract-negation theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.subtract-negation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
