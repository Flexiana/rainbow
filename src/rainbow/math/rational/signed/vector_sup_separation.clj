(ns rainbow.math.rational.signed.vector-sup-separation
  "Zero separation for signed-list sup distance at fixed shape.

  Componentwise vector equivalence always implies zero sup distance.  The
  converse needs `vector/same-shape`, because this truncating representation
  assigns zero distance when either list is empty.  Together the directions
  give the exact fixed-dimension separation law.  Native, kernel-checked, and
  axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & xs] (apply function/app f xs))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))
(defn- absurd [target impossible]
  (app impossible target))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- antisymmetric [left right first second]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right first second))

(def sup-distance-zero-of-equivalent-spec
  {:name 'vector/sup-distance-zero-of-equivalent :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (veq (sup-distance 'left 'right) signed-zero))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]]
            (veq (sup-distance 'current-left 'current-right)
                 signed-zero)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]]
                  (veq (sup-distance empty 'current-right)
                       signed-zero)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]]
               (equivalent-reflexive signed-zero))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (veq
                  (sup-distance
                   empty (cons-vector 'right-head 'right-tail))
                  signed-zero)
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-zero (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]]
                   (veq (sup-distance current-left 'current-right)
                        signed-zero)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]]
                (absurd
                 (veq (sup-distance current-left (nil-vector)) signed-zero)
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (vector-equivalent
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-same
                       (proposition-left
                        (veq 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (veq 'left-head 'right-head)
                        (vector-equivalent 'left-tail 'right-tail)
                        'current-same)
                       head-zero
                       (app
                        (function/const*
                         'signed/distance-zero-of-equivalent [])
                        'left-head 'right-head head-same)
                       recursive-zero
                       (app 'tail-zero 'right-tail tail-same)
                       current-maximum
                       (maximum
                        (scalar-distance 'left-head 'right-head)
                        (sup-distance 'left-tail 'right-tail))
                       zero-maximum (maximum signed-zero signed-zero)]
                   (app
                    (function/const* 'signed/equivalent-transitive [])
                    current-maximum zero-maximum signed-zero
                    (app
                     (function/const*
                      'signed/max-respects-equivalence [])
                     (scalar-distance 'left-head 'right-head)
                     (sup-distance 'left-tail 'right-tail)
                     signed-zero signed-zero
                     head-zero recursive-zero)
                    (function/const* 'signed/absolute-zero [])))))
               'current-right))))]
      (app
       (list-rec outer-motive outer-base outer-step 'left)
       'right 'same)))})

(def equivalent-of-sup-distance-zero-spec
  {:name 'vector/equivalent-of-sup-distance-zero :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['distance-zero (veq (sup-distance 'left 'right) signed-zero)]]
    (vector-equivalent 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]
     ['distance-zero (veq (sup-distance 'left 'right) signed-zero)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-shape
              (same-shape 'current-left 'current-right)]
             ['current-distance-zero
              (veq (sup-distance 'current-left 'current-right)
                   signed-zero)]]
            (vector-equivalent 'current-left 'current-right)))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-shape (same-shape empty 'current-right)]
                   ['current-distance-zero
                    (veq (sup-distance empty 'current-right)
                         signed-zero)]]
                  (vector-equivalent empty 'current-right)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-shape (same-shape empty empty)]
                ['current-distance-zero
                 (veq (sup-distance empty empty) signed-zero)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-shape
                  (same-shape
                   empty (cons-vector 'right-head 'right-tail))]
                 ['current-distance-zero
                  (veq
                   (sup-distance
                    empty (cons-vector 'right-head 'right-tail))
                   signed-zero)]]
                (absurd
                 (vector-equivalent
                  empty (cons-vector 'right-head 'right-tail))
                 'current-shape)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-reflects (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-shape
                     (same-shape current-left 'current-right)]
                    ['current-distance-zero
                     (veq (sup-distance current-left 'current-right)
                          signed-zero)]]
                   (vector-equivalent current-left 'current-right)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-shape
                  (same-shape current-left (nil-vector))]
                 ['current-distance-zero
                  (veq (sup-distance current-left (nil-vector))
                       signed-zero)]]
                (absurd
                 (vector-equivalent current-left (nil-vector))
                 'current-shape))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-shape
                   (same-shape
                    current-left
                    (cons-vector 'right-head 'right-tail))]
                  ['current-distance-zero
                   (veq
                    (sup-distance
                     current-left
                     (cons-vector 'right-head 'right-tail))
                    signed-zero)]]
                 (let [head-zero-proposition
                       (veq signed-zero signed-zero)
                       tail-shape
                       (same-shape 'left-tail 'right-tail)
                       recursive-shape
                       (proposition-right
                        head-zero-proposition tail-shape
                        'current-shape)
                       head-distance
                       (scalar-distance 'left-head 'right-head)
                       tail-distance
                       (sup-distance 'left-tail 'right-tail)
                       current-maximum
                       (maximum head-distance tail-distance)
                       maximum-below-zero
                       (app
                        (function/const* 'signed/equivalent-to-at-most [])
                        current-maximum signed-zero
                        'current-distance-zero)
                       head-below-zero
                       (order-transitive
                        head-distance current-maximum signed-zero
                        (app (function/const* 'signed/max-upper-left [])
                             head-distance tail-distance)
                        maximum-below-zero)
                       tail-below-zero
                       (order-transitive
                        tail-distance current-maximum signed-zero
                        (app (function/const* 'signed/max-upper-right [])
                             head-distance tail-distance)
                        maximum-below-zero)
                       head-zero
                       (antisymmetric
                        head-distance signed-zero
                        head-below-zero
                        (app
                         (function/const* 'signed/distance-nonnegative [])
                         'left-head 'right-head))
                       recursive-zero
                       (antisymmetric
                        tail-distance signed-zero
                        tail-below-zero
                        (app
                         (function/const*
                          'vector/sup-distance-nonnegative [])
                         'left-tail 'right-tail))
                       head-same
                       (app
                        (function/const*
                         'signed/equivalent-of-distance-zero [])
                        'left-head 'right-head head-zero)
                       tail-same
                       (app
                        'tail-reflects 'right-tail
                        recursive-shape recursive-zero)]
                   (conjoin
                    (veq 'left-head 'right-head)
                    (vector-equivalent 'left-tail 'right-tail)
                    head-same tail-same))))
               'current-right))))]
      (app
       (list-rec outer-motive outer-base outer-step 'left)
       'right 'shape 'distance-zero)))})

(def sup-distance-zero-iff-equivalent-same-shape-spec
  {:name 'vector/sup-distance-zero-iff-equivalent-same-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (proposition/equivalence
     (veq (sup-distance 'left 'right) signed-zero)
     (vector-equivalent 'left 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (let [distance-zero (veq (sup-distance 'left 'right) signed-zero)
          same (vector-equivalent 'left 'right)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       distance-zero same
       (function/lam
        [['zero-distance distance-zero]]
        (app
         (function/const*
          'vector/equivalent-of-sup-distance-zero [])
         'left 'right 'shape 'zero-distance))
       (function/lam
        [['equivalent same]]
        (app
         (function/const*
          'vector/sup-distance-zero-of-equivalent [])
         'left 'right 'equivalent)))))})

(def definition-specs [])
(def theorem-specs
  [sup-distance-zero-of-equivalent-spec
   equivalent-of-sup-distance-zero-spec
   sup-distance-zero-iff-equivalent-same-shape-spec])

(defn extend-environment [env]
  (-> env
      sup/extend-environment
      shape/extend-environment
      (support/extend-with :signed-vector-sup-separation theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
