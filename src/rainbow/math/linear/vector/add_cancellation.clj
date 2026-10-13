(ns rainbow.math.linear.vector.add-cancellation
  "Shape-safe cancellation of a common vector from equivalence and order.

  Because native vector/add truncates, both operands must have the offset's
  shape.  Under those hypotheses a common right or left addend cancels from
  vector equivalence and from vector/at-most.  Proofs compose existing checked
  arithmetic and order laws; there is no new recursion."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-add :as shape-add]))

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
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def equivalent-add-right-cancel-spec
  {:name 'vector/equivalent-add-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-add 'left 'offset)
       (vector-add 'right 'offset))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-add 'left 'offset)
       (vector-add 'right 'offset))]]
    (let [left-sum (vector-add 'left 'offset)
          right-sum (vector-add 'right 'offset)
          negated-offset (vector-negate 'offset)
          left-cancelled (vector-subtract left-sum 'offset)
          right-cancelled (vector-subtract right-sum 'offset)
          translated
          (app (function/const* 'vector/add-respects-equivalence [])
               left-sum right-sum
               negated-offset negated-offset
               'same
               (app (function/const* 'vector/equivalent-reflexive [])
                    negated-offset))
          left-reduces
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'left 'offset 'left-shape)
          left-expands
          (app (function/const* 'vector/equivalent-symmetric [])
               left-cancelled 'left left-reduces)
          right-reduces
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'right 'offset 'right-shape)]
      (app
       (function/const* 'vector/equivalent-transitive [])
       'left right-cancelled 'right
       (app (function/const* 'vector/equivalent-transitive [])
            'left left-cancelled right-cancelled
            left-expands translated)
       right-reduces)))})

(def equivalent-add-left-cancel-spec
  {:name 'vector/equivalent-add-left-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-add 'offset 'left)
       (vector-add 'offset 'right))]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['same
      (vector-equivalent
       (vector-add 'offset 'left)
       (vector-add 'offset 'right))]]
    (let [left-right-sum (vector-add 'left 'offset)
          left-left-sum (vector-add 'offset 'left)
          right-left-sum (vector-add 'offset 'right)
          right-right-sum (vector-add 'right 'offset)
          align-right
          (app (function/const* 'vector/equivalent-symmetric [])
               right-right-sum right-left-sum
               (app (function/const* 'vector/add-commutative [])
                    'right 'offset))
          aligned
          (app
           (function/const* 'vector/equivalent-transitive [])
           left-right-sum right-left-sum right-right-sum
           (app (function/const* 'vector/equivalent-transitive [])
                left-right-sum left-left-sum right-left-sum
                (app (function/const* 'vector/add-commutative [])
                     'left 'offset)
                'same)
           align-right)]
      (app (function/const* 'vector/equivalent-add-right-cancel [])
           'left 'right 'offset
           'left-shape 'right-shape aligned)))})

(def at-most-add-right-cancel-spec
  {:name 'vector/at-most-add-right-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-add 'left 'offset)
       (vector-add 'right 'offset))]]
    (vector-at-most 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-add 'left 'offset)
       (vector-add 'right 'offset))]]
    (let [left-sum (vector-add 'left 'offset)
          right-sum (vector-add 'right 'offset)
          negated-offset (vector-negate 'offset)
          left-cancelled (vector-subtract left-sum 'offset)
          right-cancelled (vector-subtract right-sum 'offset)
          translated
          (app (function/const* 'vector/add-right-monotone [])
               left-sum right-sum negated-offset 'ordered)
          left-equivalent
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'left 'offset 'left-shape)
          left-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               left-cancelled 'left left-equivalent)
          left-to-cancelled
          (proposition-right
           (vector-at-most left-cancelled 'left)
           (vector-at-most 'left left-cancelled)
           left-bounds)
          right-equivalent
          (app (function/const* 'vector/add-subtract-right-cancel [])
               'right 'offset 'right-shape)
          right-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               right-cancelled 'right right-equivalent)
          cancelled-to-right
          (proposition-left
           (vector-at-most right-cancelled 'right)
           (vector-at-most 'right right-cancelled)
           right-bounds)]
      (app
       (function/const* 'vector/at-most-transitive [])
       'left right-cancelled 'right
       (app (function/const* 'vector/at-most-transitive [])
            'left left-cancelled right-cancelled
            left-to-cancelled translated)
       cancelled-to-right)))})

(def at-most-add-left-cancel-spec
  {:name 'vector/at-most-add-left-cancel :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-add 'offset 'left)
       (vector-add 'offset 'right))]]
    (vector-at-most 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['left-shape (same-shape 'left 'offset)]
     ['right-shape (same-shape 'right 'offset)]
     ['ordered
      (vector-at-most
       (vector-add 'offset 'left)
       (vector-add 'offset 'right))]]
    (let [left-right-sum (vector-add 'left 'offset)
          left-left-sum (vector-add 'offset 'left)
          right-left-sum (vector-add 'offset 'right)
          right-right-sum (vector-add 'right 'offset)
          align-left
          (app (function/const* 'vector/equivalent-to-at-most [])
               left-right-sum left-left-sum
               (app (function/const* 'vector/add-commutative [])
                    'left 'offset))
          align-right-equivalent
          (app (function/const* 'vector/equivalent-symmetric [])
               right-right-sum right-left-sum
               (app (function/const* 'vector/add-commutative [])
                    'right 'offset))
          align-right
          (app (function/const* 'vector/equivalent-to-at-most [])
               right-left-sum right-right-sum
               align-right-equivalent)
          aligned-order
          (app
           (function/const* 'vector/at-most-transitive [])
           left-right-sum right-left-sum right-right-sum
           (app (function/const* 'vector/at-most-transitive [])
                left-right-sum left-left-sum right-left-sum
                align-left 'ordered)
           align-right)]
      (app (function/const* 'vector/at-most-add-right-cancel [])
           'left 'right 'offset
           'left-shape 'right-shape aligned-order)))})

(def definition-specs [])
(def theorem-specs
  [equivalent-add-right-cancel-spec
   equivalent-add-left-cancel-spec
   at-most-add-right-cancel-spec
   at-most-add-left-cancel-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      shape-add/extend-environment
      (support/extend-with :vector-add-cancellation theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
