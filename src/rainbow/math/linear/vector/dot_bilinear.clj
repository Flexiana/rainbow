(ns rainbow.math.linear.vector.dot-bilinear
  "Right additivity of the native dot product, completing additive bilinearity.

    same-shape left right
      -> dot weights (left + right) ~ dot weights left + dot weights right

  Commute the outer dot, apply vector/dot-additive-left, then commute each
  resulting dot through signed addition congruence.  Native and axiom-free."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.linear.vector.dot-additive :as additive]
            [rainbow.math.linear.vector.dot-commutative :as commutative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def dot-additive-right-spec
  {:name 'vector/dot-additive-right :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (dot 'weights (vector-add 'left 'right))
     (signed-add (dot 'weights 'left) (dot 'weights 'right))))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [sum (vector-add 'left 'right)
          start (dot 'weights sum)
          commuted (dot sum 'weights)
          split (signed-add (dot 'left 'weights) (dot 'right 'weights))
          finish (signed-add (dot 'weights 'left) (dot 'weights 'right))
          commute-outer
          (app (function/const* 'vector/dot-commutative []) 'weights sum)
          split-left
          (app (function/const* 'vector/dot-additive-left [])
               'left 'right 'weights 'same)
          commute-terms
          (app (function/const* 'signed/add-respects-equivalence [])
               (dot 'left 'weights) (dot 'weights 'left)
               (dot 'right 'weights) (dot 'weights 'right)
               (app (function/const* 'vector/dot-commutative [])
                    'left 'weights)
               (app (function/const* 'vector/dot-commutative [])
                    'right 'weights))]
      (transitive
       start split finish
       (transitive start commuted split commute-outer split-left)
       commute-terms)))})

(def definition-specs [])
(def theorem-specs [dot-additive-right-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      additive/extend-environment
      (extend-spec-if-missing
       'signed/multiply-commutative :signed-multiply-ring
       signed-ring/multiply-commutative-spec)
      (extend-spec-if-missing
       'vector/dot-commutative :vector-dot-commutative
       commutative/dot-commutative-spec)
      (support/extend-with :vector-dot-bilinear theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
