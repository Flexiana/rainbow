(ns rainbow.math.linear.vector.row-sum-lipschitz
  "Nonnegative row-sum Lipschitz bounds for signed dot products.

  `vector/sum` specializes the existing polymorphic signed map-sum to a signed
  vector.  Componentwise nonnegativity makes that mass nonnegative.  Combining
  the component multiplication-distance bound with the maximum component
  distance and distributivity proves

    dot-distance-sum(row,x,y) <= sum(row) * sup-distance(x,y).

  The previously established dot-distance theorem then yields the same bound
  for the actual dot products.  Equal input shape is explicit because dot and
  sup distance both truncate lists.  Native, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-multiply-nonnegative :as weighted]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.list-sum :as signed-sum]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]
            [rainbow.math.linear.vector.dot-distance-bound :as dot-bound]
            [rainbow.math.linear.vector.pointwise-order :as pointwise]))

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
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- vector-positive [values]
  (vector-at-most (zero-like values) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- dot [weights values]
  (app (function/const* 'vector/dot []) weights values))
(defn- distance-sum [weights left right]
  (app (function/const* 'vector/dot-distance-sum [])
       weights left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- map-sum [mapping values]
  (app (function/const* 'signed/map-sum [zero-level])
       signed mapping values))
(defn- proposition-left [left right evidence]
  (app (function/const* 'proposition/left []) left right evidence))
(defn- proposition-right [left right evidence]
  (app (function/const* 'proposition/right []) left right evidence))
(defn- absurd [target impossible]
  (app impossible target))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- order-transitive [left middle right first second]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right first second))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- multiply-nonnegative-at-most [left right left-positive right-positive]
  (let [product (multiply left right)]
    (app
     (function/const* 'signed/zero-at-most-of-nonnegative [])
     product
     (app
      (function/const* 'signed/multiply-nonnegative [])
      left right
      (app (function/const* 'signed/nonnegative-of-zero-at-most [])
           left left-positive)
      (app (function/const* 'signed/nonnegative-of-zero-at-most [])
           right right-positive)))))

(def vector-sum-spec
  {:name 'vector/sum :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type signed)
   :value
   (function/lam
    [['values vector-type]]
    (map-sum (function/lam [['value signed]] 'value) 'values))})

(def vector-sum-nonnegative-spec
  {:name 'vector/sum-nonnegative :universes []
   :type
   (function/forall
    [['values vector-type]
     ['positive (vector-positive 'values)]]
    (sle signed-zero (vector-sum 'values)))
   :value
   (function/lam
    [['values vector-type]
     ['positive (vector-positive 'values)]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (function/arrow
            (vector-positive 'current)
            (sle signed-zero (vector-sum 'current))))
          base
          (function/lam
           [['ignored (vector-positive (nil-vector))]]
           (order-reflexive signed-zero))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-nonnegative
             (function/arrow
              (vector-positive 'tail)
              (sle signed-zero (vector-sum 'tail)))]
            ['current-positive
             (vector-positive (cons-vector 'head 'tail))]]
           (let [head-positive (sle signed-zero 'head)
                 tail-positive (vector-positive 'tail)
                 total (add 'head (vector-sum 'tail))
                 zero-plus-zero (add signed-zero signed-zero)
                 combined
                 (app (function/const* 'signed/add-monotone [])
                      signed-zero 'head
                      signed-zero (vector-sum 'tail)
                      (proposition-left
                       head-positive tail-positive 'current-positive)
                      (app
                       'tail-nonnegative
                       (proposition-right
                        head-positive tail-positive
                        'current-positive)))]
             (order-respects
              zero-plus-zero signed-zero total total
              (app (function/const* 'signed/add-zero-right [])
                   signed-zero)
              (equivalent-reflexive total)
              combined))) ]
      (app (list-rec motive base step 'values) 'positive)))})

(def dot-distance-sum-bounded-by-row-sum-spec
  {:name 'vector/dot-distance-sum-bounded-by-row-sum :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vector-positive 'weights)]
     ['shape (same-shape 'left 'right)]]
    (sle
     (distance-sum 'weights 'left 'right)
     (multiply (vector-sum 'weights)
               (sup-distance 'left 'right))))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vector-positive 'weights)]
     ['shape (same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-weights vector-type]]
           (function/forall
            [['current-left vector-type] ['current-right vector-type]
             ['current-positive (vector-positive 'current-weights)]
             ['current-shape
              (same-shape 'current-left 'current-right)]]
            (sle
             (distance-sum
              'current-weights 'current-left 'current-right)
             (multiply
              (vector-sum 'current-weights)
              (sup-distance 'current-left 'current-right)))))
          outer-base
          (function/lam
           [['current-left vector-type] ['current-right vector-type]
            ['current-positive (vector-positive (nil-vector))]
            ['current-shape
             (same-shape 'current-left 'current-right)]]
           (multiply-nonnegative-at-most
            signed-zero
            (sup-distance 'current-left 'current-right)
            (order-reflexive signed-zero)
            (app
             (function/const* 'vector/sup-distance-nonnegative [])
             'current-left 'current-right)))
          outer-step
          (function/lam
           [['weight-head signed] ['weight-tail vector-type]
            ['tail-bound (app outer-motive 'weight-tail)]]
           (let [current-weights
                 (cons-vector 'weight-head 'weight-tail)
                 left-motive
                 (function/lam
                  [['current-left vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-positive
                     (vector-positive current-weights)]
                    ['current-shape
                     (same-shape 'current-left 'current-right)]]
                   (sle
                    (distance-sum
                     current-weights 'current-left 'current-right)
                    (multiply
                     (vector-sum current-weights)
                     (sup-distance
                      'current-left 'current-right)))))]
             (function/lam
              [['current-left vector-type]]
              (list-rec
               left-motive
               (let [empty (nil-vector)
                     right-motive
                     (function/lam
                      [['current-right vector-type]]
                      (function/forall
                       [['current-positive
                         (vector-positive current-weights)]
                        ['current-shape
                         (same-shape empty 'current-right)]]
                       (sle
                        (distance-sum
                         current-weights empty 'current-right)
                        (multiply
                         (vector-sum current-weights)
                         (sup-distance empty 'current-right)))))]
                 (function/lam
                  [['current-right vector-type]]
                  (list-rec
                   right-motive
                   (function/lam
                    [['current-positive
                      (vector-positive current-weights)]
                     ['current-shape (same-shape empty empty)]]
                    (multiply-nonnegative-at-most
                     (vector-sum current-weights) signed-zero
                     (app (function/const* 'vector/sum-nonnegative [])
                          current-weights 'current-positive)
                     (order-reflexive signed-zero)))
                   (function/lam
                    [['right-head signed] ['right-tail vector-type]
                     ['ignored-right (app right-motive 'right-tail)]]
                    (function/lam
                     [['current-positive
                       (vector-positive current-weights)]
                      ['current-shape
                       (same-shape
                        empty (cons-vector 'right-head 'right-tail))]]
                     (absurd
                      (sle
                       (distance-sum
                        current-weights empty
                        (cons-vector 'right-head 'right-tail))
                       (multiply
                        (vector-sum current-weights)
                        (sup-distance
                         empty
                         (cons-vector 'right-head 'right-tail))))
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
                        [['current-positive
                          (vector-positive current-weights)]
                         ['current-shape
                          (same-shape current-left 'current-right)]]
                        (sle
                         (distance-sum
                          current-weights current-left 'current-right)
                         (multiply
                          (vector-sum current-weights)
                          (sup-distance
                           current-left 'current-right)))))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-positive
                       (vector-positive current-weights)]
                      ['current-shape
                       (same-shape current-left (nil-vector))]]
                     (absurd
                      (sle
                       (distance-sum
                        current-weights current-left (nil-vector))
                       (multiply
                        (vector-sum current-weights)
                        (sup-distance
                         current-left (nil-vector))))
                      'current-shape))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (let [current-right
                           (cons-vector 'right-head 'right-tail)]
                       (function/lam
                        [['current-positive
                          (vector-positive current-weights)]
                         ['current-shape
                          (same-shape current-left current-right)]]
                        (let [head-positive-proposition
                              (sle signed-zero 'weight-head)
                              tail-positive-proposition
                              (vector-positive 'weight-tail)
                              head-positive
                              (proposition-left
                               head-positive-proposition
                               tail-positive-proposition
                               'current-positive)
                              tail-positive
                              (proposition-right
                               head-positive-proposition
                               tail-positive-proposition
                               'current-positive)
                              head-zero (veq signed-zero signed-zero)
                              tail-shape-proposition
                              (same-shape 'left-tail 'right-tail)
                              tail-shape
                              (proposition-right
                               head-zero tail-shape-proposition
                               'current-shape)
                              head-distance
                              (scalar-distance 'left-head 'right-head)
                              tail-sup
                              (sup-distance 'left-tail 'right-tail)
                              full-sup
                              (maximum head-distance tail-sup)
                              product-distance
                              (scalar-distance
                               (multiply 'weight-head 'left-head)
                               (multiply 'weight-head 'right-head))
                              tail-distance-sum
                              (distance-sum
                               'weight-tail 'left-tail 'right-tail)
                              tail-mass (vector-sum 'weight-tail)
                              weighted-head
                              (multiply 'weight-head head-distance)
                              weighted-tail
                              (multiply tail-mass tail-sup)
                              expanded-head
                              (multiply 'weight-head full-sup)
                              expanded-tail
                              (multiply tail-mass full-sup)
                              component-sum
                              (add product-distance tail-distance-sum)
                              weighted-sum
                              (add weighted-head weighted-tail)
                              expanded-sum
                              (add expanded-head expanded-tail)
                              target
                              (multiply
                               (add 'weight-head tail-mass)
                               full-sup)
                              component-bound
                              (app
                               (function/const*
                                'signed/distance-multiply-left-nonnegative [])
                               'weight-head 'left-head 'right-head
                               head-positive)
                              tail-distance-bound
                              (app
                               'tail-bound
                               'left-tail 'right-tail
                               tail-positive tail-shape)
                              first-bound
                              (app (function/const* 'signed/add-monotone [])
                                   product-distance weighted-head
                                   tail-distance-sum weighted-tail
                                   component-bound tail-distance-bound)
                              tail-mass-positive
                              (app (function/const* 'vector/sum-nonnegative [])
                                   'weight-tail tail-positive)
                              head-expanded-bound
                              (app
                               (function/const*
                                'signed/multiply-left-monotone [])
                               'weight-head head-distance full-sup
                               head-positive
                               (app
                                (function/const* 'signed/max-upper-left [])
                                head-distance tail-sup))
                              tail-expanded-bound
                              (app
                               (function/const*
                                'signed/multiply-left-monotone [])
                               tail-mass tail-sup full-sup
                               tail-mass-positive
                               (app
                                (function/const* 'signed/max-upper-right [])
                                head-distance tail-sup))
                              second-bound
                              (app (function/const* 'signed/add-monotone [])
                                   weighted-head expanded-head
                                   weighted-tail expanded-tail
                                   head-expanded-bound tail-expanded-bound)
                              distributed
                              (app
                               (function/const*
                                'signed/multiply-distributes-add-right [])
                               'weight-head tail-mass full-sup)
                              expanded-target-same
                              (equivalent-symmetric
                               target expanded-sum distributed)
                              final-bound
                              (app
                               (function/const* 'signed/equivalent-to-at-most [])
                               expanded-sum target expanded-target-same)]
                          (order-transitive
                           component-sum expanded-sum target
                           (order-transitive
                            component-sum weighted-sum expanded-sum
                            first-bound second-bound)
                           final-bound)))))
                    'current-right))))
               'current-left))))]
      (app
       (list-rec outer-motive outer-base outer-step 'weights)
       'left 'right 'weights-positive 'shape)))})

(def dot-distance-bounded-by-row-sum-spec
  {:name 'vector/dot-distance-bounded-by-row-sum :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vector-positive 'weights)]
     ['shape (same-shape 'left 'right)]]
    (sle
     (scalar-distance (dot 'weights 'left)
                      (dot 'weights 'right))
     (multiply (vector-sum 'weights)
               (sup-distance 'left 'right))))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['weights-positive (vector-positive 'weights)]
     ['shape (same-shape 'left 'right)]]
    (order-transitive
     (scalar-distance (dot 'weights 'left)
                      (dot 'weights 'right))
     (distance-sum 'weights 'left 'right)
     (multiply (vector-sum 'weights)
               (sup-distance 'left 'right))
     (app (function/const* 'vector/dot-distance-below-sum [])
          'weights 'left 'right 'shape)
     (app
      (function/const*
       'vector/dot-distance-sum-bounded-by-row-sum [])
      'weights 'left 'right 'weights-positive 'shape)))})

(def definition-specs [vector-sum-spec])
(def theorem-specs
  [vector-sum-nonnegative-spec
   dot-distance-sum-bounded-by-row-sum-spec
   dot-distance-bounded-by-row-sum-spec])

(defn extend-environment [env]
  (-> env
      signed-sum/extend-environment
      pointwise/extend-environment
      weighted/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      distributive/extend-environment
      sup/extend-environment
      dot-bound/extend-environment
      (support/extend-with :vector-row-sum-lipschitz
                           (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
