(ns rainbow.math.linear.vector.dot-subtract
  "Subtraction laws for signed values and the native vector dot product.

    signed/subtract-respects-equivalence
    vector/dot-subtract-left
    vector/dot-subtract-right

  Native vector subtraction zips its arguments, so dot subtraction requires an
  explicit same-shape hypothesis: without it, the subtraction can discard a
  suffix that a separately computed dot product would retain.  Under that
  hypothesis, left subtraction follows from dot additivity and dot negation;
  the right law follows by dot commutativity."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.dot-negate :as negate]
            [rainbow.math.linear.vector.shape-map :as shape-map]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def subtract-respects-equivalence-spec
  {:name 'signed/subtract-respects-equivalence :universes []
   :type
   (function/forall
    [['left signed] ['left-prime signed]
     ['right signed] ['right-prime signed]
     ['left-same (signed-equivalent 'left 'left-prime)]
     ['right-same (signed-equivalent 'right 'right-prime)]]
    (signed-equivalent
     (signed-subtract 'left 'right)
     (signed-subtract 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left signed] ['left-prime signed]
     ['right signed] ['right-prime signed]
     ['left-same (signed-equivalent 'left 'left-prime)]
     ['right-same (signed-equivalent 'right 'right-prime)]]
    (app (function/const* 'signed/add-respects-equivalence [])
         'left 'left-prime
         (signed-negate 'right) (signed-negate 'right-prime)
         'left-same
         (app (function/const* 'signed/negate-respects-equivalence [])
              'right 'right-prime 'right-same)))})

(def dot-subtract-left-spec
  {:name 'vector/dot-subtract-left :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (dot (vector-subtract 'left 'right) 'weights)
     (signed-subtract (dot 'left 'weights) (dot 'right 'weights))))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['weights vector-type]
     ['same (same-shape 'left 'right)]]
    (let [negated-right (vector-negate 'right)
          start (dot (vector-add 'left negated-right) 'weights)
          split
          (signed-add
           (dot 'left 'weights)
           (dot negated-right 'weights))
          finish
          (signed-add
           (dot 'left 'weights)
           (signed-negate (dot 'right 'weights)))
          right-to-negated-right
          (app (function/const* 'vector/same-shape-symmetric [])
               negated-right 'right
               (app (function/const* 'vector/negate-preserves-shape [])
                    'right))
          add-shape
          (app (function/const* 'vector/same-shape-transitive [])
               'left 'right negated-right
               'same right-to-negated-right)
          split-dot
          (app (function/const* 'vector/dot-additive-left [])
               'left negated-right 'weights add-shape)
          replace-negated-dot
          (app (function/const* 'signed/add-respects-equivalence [])
               (dot 'left 'weights) (dot 'left 'weights)
               (dot negated-right 'weights)
               (signed-negate (dot 'right 'weights))
               (app (function/const* 'signed/equivalent-reflexive [])
                    (dot 'left 'weights))
               (app (function/const* 'vector/dot-negate-left [])
                    'right 'weights))]
      (transitive
       start split finish split-dot replace-negated-dot)))})

(def dot-subtract-right-spec
  {:name 'vector/dot-subtract-right :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (signed-equivalent
     (dot 'weights (vector-subtract 'left 'right))
     (signed-subtract (dot 'weights 'left) (dot 'weights 'right))))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (same-shape 'left 'right)]]
    (let [difference (vector-subtract 'left 'right)
          start (dot 'weights difference)
          commuted (dot difference 'weights)
          split
          (signed-subtract
           (dot 'left 'weights) (dot 'right 'weights))
          finish
          (signed-subtract
           (dot 'weights 'left) (dot 'weights 'right))]
      (transitive
       start split finish
       (transitive
        start commuted split
        (app (function/const* 'vector/dot-commutative [])
             'weights difference)
        (app (function/const* 'vector/dot-subtract-left [])
             'left 'right 'weights 'same))
       (app (function/const* 'signed/subtract-respects-equivalence [])
            (dot 'left 'weights) (dot 'weights 'left)
            (dot 'right 'weights) (dot 'weights 'right)
            (app (function/const* 'vector/dot-commutative [])
                 'left 'weights)
            (app (function/const* 'vector/dot-commutative [])
                 'right 'weights)))))})

(def definition-specs [])
(def theorem-specs
  [subtract-respects-equivalence-spec
   dot-subtract-left-spec
   dot-subtract-right-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      negate/extend-environment
      shape-map/extend-environment
      (support/extend-with :vector-dot-subtract theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
