(ns rainbow.math.linear.vector.norm-expansion
  "Exact quadratic expansions for the native signed squared norm.

    norm/norm-squared-add
    norm/norm-squared-subtract

  For same-shaped vectors, squared norm expands into the four expected dot
  terms.  The subtraction law retains nested signed subtraction, which is the
  exact Grothendieck-pair form of a^2 - a*b - b*a + b^2.  Both results are
  theorem-only compositions of dot additivity/subtractivity."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.dot-subtract :as dot-subtract]
            [rainbow.math.linear.vector.norm :as norm]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def norm-squared-add-spec
  {:name 'norm/norm-squared-add :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (norm-squared (vector-add 'left 'right))
     (signed-add
      (signed-add (norm-squared 'left) (dot 'left 'right))
      (signed-add (dot 'right 'left) (norm-squared 'right)))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [sum (vector-add 'left 'right)
          start (norm-squared sum)
          split
          (signed-add (dot 'left sum) (dot 'right sum))
          finish
          (signed-add
           (signed-add (norm-squared 'left) (dot 'left 'right))
           (signed-add (dot 'right 'left) (norm-squared 'right)))
          split-outer
          (app (function/const* 'vector/dot-additive-left [])
               'left 'right sum 'same)
          split-inner
          (app (function/const* 'signed/add-respects-equivalence [])
               (dot 'left sum)
               (signed-add (dot 'left 'left) (dot 'left 'right))
               (dot 'right sum)
               (signed-add (dot 'right 'left) (dot 'right 'right))
               (app (function/const* 'vector/dot-additive-right [])
                    'left 'left 'right 'same)
               (app (function/const* 'vector/dot-additive-right [])
                    'right 'left 'right 'same))]
      (transitive start split finish split-outer split-inner)))})

(def norm-squared-subtract-spec
  {:name 'norm/norm-squared-subtract :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (norm-squared (vector-subtract 'left 'right))
     (signed-subtract
      (signed-subtract (norm-squared 'left) (dot 'left 'right))
      (signed-subtract (dot 'right 'left) (norm-squared 'right)))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [difference (vector-subtract 'left 'right)
          start (norm-squared difference)
          split
          (signed-subtract
           (dot 'left difference) (dot 'right difference))
          finish
          (signed-subtract
           (signed-subtract (norm-squared 'left) (dot 'left 'right))
           (signed-subtract (dot 'right 'left) (norm-squared 'right)))
          split-outer
          (app (function/const* 'vector/dot-subtract-left [])
               'left 'right difference 'same)
          split-inner
          (app (function/const* 'signed/subtract-respects-equivalence [])
               (dot 'left difference)
               (signed-subtract (dot 'left 'left) (dot 'left 'right))
               (dot 'right difference)
               (signed-subtract (dot 'right 'left) (dot 'right 'right))
               (app (function/const* 'vector/dot-subtract-right [])
                    'left 'left 'right 'same)
               (app (function/const* 'vector/dot-subtract-right [])
                    'right 'left 'right 'same))]
      (transitive start split finish split-outer split-inner)))})

(def definition-specs [])
(def theorem-specs
  [norm-squared-add-spec norm-squared-subtract-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      dot-subtract/extend-environment
      norm/extend-environment
      (support/extend-with :vector-norm-expansion theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
