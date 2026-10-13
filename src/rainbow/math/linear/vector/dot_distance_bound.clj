(ns rainbow.math.linear.vector.dot-distance-bound
  "Componentwise distance accounting for signed dot products.

  `vector/dot-distance-sum weights left right` sums the distances between
  corresponding weighted components.  When `left` and `right` have the same
  shape, paired-addition Lipschitzness proves that the distance between their
  dot products is below this explicit sum.  A second theorem transfers any
  upper bound on the sum to the dot distance.  The shape premise is essential:
  truncating dot products can otherwise consume different weight prefixes.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.algorithms.proofs.inner-product :as inner-product]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-additive :as additive]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

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
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- distance-sum [weights left right]
  (app (function/const* 'vector/dot-distance-sum [])
       weights left right))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))

(def dot-distance-sum-spec
  {:name 'vector/dot-distance-sum :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type vector-type signed)
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      signed
      (function/lam
       [['ignored vector-type]]
       (function/arrow vector-type vector-type signed))
      (function/lam
       [['ignored-left vector-type] ['ignored-right vector-type]]
       signed-zero)
      (function/lam
       [['weight-head signed] ['weight-tail vector-type]
        ['tail-sum
         (function/arrow vector-type vector-type signed)]]
       (function/lam
        [['current-left vector-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         signed
         (function/lam
          [['ignored vector-type]]
          (function/arrow vector-type signed))
         (function/lam [['ignored-right vector-type]] signed-zero)
         (function/lam
          [['left-head signed] ['left-tail vector-type]
           ['ignored-left-tail (function/arrow vector-type signed)]]
          (function/lam
           [['current-right vector-type]]
           (app
            (function/const* 'data/List.rec [type-level type-level])
            signed
            (function/lam [['ignored vector-type]] signed)
            signed-zero
            (function/lam
             [['right-head signed] ['right-tail vector-type]
              ['ignored-right-tail signed]]
             (add
              (scalar-distance
               (multiply 'weight-head 'left-head)
               (multiply 'weight-head 'right-head))
              (app 'tail-sum 'left-tail 'right-tail)))
            'current-right)))
         'current-left)))
      'weights)
     'left 'right))})

(def dot-distance-below-sum-spec
  {:name 'vector/dot-distance-below-sum :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (sle (scalar-distance (dot 'weights 'left)
                          (dot 'weights 'right))
         (distance-sum 'weights 'left 'right)))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['shape (same-shape 'left 'right)]]
    (let [zero-bound
          (fn []
            (app (function/const* 'signed/equivalent-to-at-most [])
                 (scalar-distance signed-zero signed-zero)
                 signed-zero
                 (app (function/const* 'signed/distance-self-zero [])
                      signed-zero)))
          outer-motive
          (function/lam
           [['current-weights vector-type]]
           (function/forall
            [['current-left vector-type] ['current-right vector-type]
             ['current-shape
              (same-shape 'current-left 'current-right)]]
            (sle
             (scalar-distance
              (dot 'current-weights 'current-left)
              (dot 'current-weights 'current-right))
             (distance-sum
              'current-weights 'current-left 'current-right))))
          outer-base
          (function/lam
           [['current-left vector-type] ['current-right vector-type]
            ['current-shape
             (same-shape 'current-left 'current-right)]]
           (zero-bound))
          outer-step
          (function/lam
           [['weight-head signed] ['weight-tail vector-type]
            ['tail-bounded (app outer-motive 'weight-tail)]]
           (let [current-weights
                 (cons-vector 'weight-head 'weight-tail)
                 left-motive
                 (function/lam
                  [['current-left vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-shape
                     (same-shape 'current-left 'current-right)]]
                   (sle
                    (scalar-distance
                     (dot current-weights 'current-left)
                     (dot current-weights 'current-right))
                    (distance-sum
                     current-weights 'current-left 'current-right))))]
             (function/lam
              [['current-left vector-type]]
              (list-rec
               left-motive
               (let [empty (nil-vector)
                     right-motive
                     (function/lam
                      [['current-right vector-type]]
                      (function/forall
                       [['current-shape
                         (same-shape empty 'current-right)]]
                       (sle
                        (scalar-distance
                         (dot current-weights empty)
                         (dot current-weights 'current-right))
                        (distance-sum
                         current-weights empty 'current-right))))]
                 (function/lam
                  [['current-right vector-type]]
                  (list-rec
                   right-motive
                   (function/lam
                    [['current-shape (same-shape empty empty)]]
                    (zero-bound))
                   (function/lam
                    [['right-head signed] ['right-tail vector-type]
                     ['ignored-right (app right-motive 'right-tail)]]
                    (function/lam
                     [['current-shape
                       (same-shape
                        empty (cons-vector 'right-head 'right-tail))]]
                     (absurd
                      (sle
                       (scalar-distance
                        (dot current-weights empty)
                        (dot current-weights
                             (cons-vector 'right-head 'right-tail)))
                       (distance-sum
                        current-weights empty
                        (cons-vector 'right-head 'right-tail)))
                      'current-shape)))
                   'current-right)))
               (function/lam
                [['left-head signed] ['left-tail vector-type]
                 ['ignored-left (app left-motive 'left-tail)]]
                (let [current-left
                      (cons-vector 'left-head 'left-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (function/forall
                        [['current-shape
                          (same-shape current-left 'current-right)]]
                        (sle
                         (scalar-distance
                          (dot current-weights current-left)
                          (dot current-weights 'current-right))
                         (distance-sum
                          current-weights current-left 'current-right))))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-shape
                       (same-shape current-left (nil-vector))]]
                     (absurd
                      (sle
                       (scalar-distance
                        (dot current-weights current-left)
                        (dot current-weights (nil-vector)))
                       (distance-sum
                        current-weights current-left (nil-vector)))
                      'current-shape))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (let [current-right
                           (cons-vector 'right-head 'right-tail)]
                       (function/lam
                        [['current-shape
                          (same-shape current-left current-right)]]
                        (let [head-zero (veq signed-zero signed-zero)
                              tail-shape
                              (same-shape 'left-tail 'right-tail)
                              current-tail-shape
                              (proposition-right
                               head-zero tail-shape 'current-shape)
                              left-product
                              (multiply 'weight-head 'left-head)
                              right-product
                              (multiply 'weight-head 'right-head)
                              head-distance
                              (scalar-distance left-product right-product)
                              left-tail-dot
                              (dot 'weight-tail 'left-tail)
                              right-tail-dot
                              (dot 'weight-tail 'right-tail)
                              tail-distance
                              (scalar-distance
                               left-tail-dot right-tail-dot)
                              tail-budget
                              (distance-sum
                               'weight-tail 'left-tail 'right-tail)
                              intermediate
                              (add head-distance tail-distance)
                              target
                              (add head-distance tail-budget)
                              additive-bound
                              (app
                               (function/const* 'signed/distance-add [])
                               left-product left-tail-dot
                               right-product right-tail-dot)
                              budget-bound
                              (app
                               (function/const* 'signed/add-monotone [])
                               head-distance head-distance
                               tail-distance tail-budget
                               (order-reflexive head-distance)
                               (app
                                'tail-bounded
                                'left-tail 'right-tail
                                current-tail-shape))]
                          (order-transitive
                           (scalar-distance
                            (add left-product left-tail-dot)
                            (add right-product right-tail-dot))
                           intermediate target
                           additive-bound budget-bound)))))
                    'current-right))))
               'current-left))))]
      (app
       (list-rec outer-motive outer-base outer-step 'weights)
       'left 'right 'shape)))})

(def dot-distance-bounded-spec
  {:name 'vector/dot-distance-bounded :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['upper signed]
     ['shape (same-shape 'left 'right)]
     ['sum-bound
      (sle (distance-sum 'weights 'left 'right) 'upper)]]
    (sle (scalar-distance (dot 'weights 'left)
                          (dot 'weights 'right))
         'upper))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['upper signed]
     ['shape (same-shape 'left 'right)]
     ['sum-bound
      (sle (distance-sum 'weights 'left 'right) 'upper)]]
    (order-transitive
     (scalar-distance (dot 'weights 'left)
                      (dot 'weights 'right))
     (distance-sum 'weights 'left 'right)
     'upper
     (app (function/const* 'vector/dot-distance-below-sum [])
          'weights 'left 'right 'shape)
     'sum-bound))})

(def definition-specs [dot-distance-sum-spec])
(def theorem-specs
  [dot-distance-below-sum-spec
   dot-distance-bounded-spec])

(defn extend-environment [env]
  (-> env
      multiply-ring/extend-environment
      inner-product/extend-environment
      additive/extend-environment
      shape/extend-environment
      (support/extend-with :vector-dot-distance-bound
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
