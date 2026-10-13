(ns rainbow.math.linear.vector.dot-congruence
  "Quotient-safe congruence of the native vector dot product.

    vector/dot-left-respects-equivalence
    vector/dot-right-respects-equivalence
    vector/dot-respects-equivalence

  The left theorem is a structural induction over two equivalent vectors and
  an arbitrary weight list.  Head products transport through signed
  multiplication congruence and tails through the induction hypothesis.  Dot
  commutativity derives the right theorem; transitivity composes both sides."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.linear.vector.dot-subtract :as subtract]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def dot-left-respects-equivalence-spec
  {:name 'vector/dot-left-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['weights vector-type]
     ['same (vector-equivalent 'left 'left-prime)]]
    (signed-equivalent
     (dot 'left 'weights) (dot 'left-prime 'weights)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['weights vector-type]
     ['same (vector-equivalent 'left 'left-prime)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-same
              (vector-equivalent 'current-left 'current-right)]
             ['current-weights vector-type]]
            (signed-equivalent
             (dot 'current-left 'current-weights)
             (dot 'current-right 'current-weights))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-same
                    (vector-equivalent empty 'current-right)]
                   ['current-weights vector-type]]
                  (signed-equivalent
                   (dot empty 'current-weights)
                   (dot 'current-right 'current-weights))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-same (vector-equivalent empty empty)]
                ['current-weights vector-type]]
               (app (function/const* 'signed/equivalent-reflexive [])
                    signed-zero))
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (vector-equivalent
                   empty (cons-vector 'right-head 'right-tail))]
                 ['current-weights vector-type]]
                (absurd
                 (signed-equivalent
                  (dot empty 'current-weights)
                  (dot (cons-vector 'right-head 'right-tail)
                       'current-weights))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-congruent (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-same
                     (vector-equivalent current-left 'current-right)]
                    ['current-weights vector-type]]
                   (signed-equivalent
                    (dot current-left 'current-weights)
                    (dot 'current-right 'current-weights))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-same
                  (vector-equivalent current-left (nil-vector))]
                 ['current-weights vector-type]]
                (absurd
                 (signed-equivalent
                  (dot current-left 'current-weights)
                  (dot (nil-vector) 'current-weights))
                 'current-same))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored-right (app right-motive 'right-tail)]]
                (let [current-right
                      (cons-vector 'right-head 'right-tail)]
                  (function/lam
                   [['current-same
                     (vector-equivalent current-left current-right)]
                    ['current-weights vector-type]]
                   (let [head-proposition
                         (signed-equivalent 'left-head 'right-head)
                         tail-proposition
                         (vector-equivalent 'left-tail 'right-tail)
                         head-same
                         (proposition-left
                          head-proposition tail-proposition 'current-same)
                         tail-same
                         (proposition-right
                          head-proposition tail-proposition 'current-same)
                         weight-motive
                         (function/lam
                          [['current-weight vector-type]]
                          (signed-equivalent
                           (dot current-left 'current-weight)
                           (dot current-right 'current-weight)))]
                     (list-rec
                      weight-motive
                      (app
                       (function/const* 'signed/equivalent-reflexive [])
                       signed-zero)
                      (function/lam
                       [['weight-head signed] ['weight-tail vector-type]
                        ['ignored-weight
                         (app weight-motive 'weight-tail)]]
                       (let [left-product
                             (signed-multiply 'left-head 'weight-head)
                             right-product
                             (signed-multiply 'right-head 'weight-head)]
                         (app
                          (function/const*
                           'signed/add-respects-equivalence [])
                          left-product right-product
                          (dot 'left-tail 'weight-tail)
                          (dot 'right-tail 'weight-tail)
                          (app
                           (function/const*
                            'signed/multiply-respects-equivalence [])
                           'left-head 'right-head
                           'weight-head 'weight-head
                           head-same
                           (app
                            (function/const*
                             'signed/equivalent-reflexive [])
                            'weight-head))
                          (app 'tail-congruent
                               'right-tail tail-same 'weight-tail))))
                      'current-weights)))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'left-prime 'same 'weights)))})

(def dot-right-respects-equivalence-spec
  {:name 'vector/dot-right-respects-equivalence :universes []
   :type
   (function/forall
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (signed-equivalent
     (dot 'weights 'left) (dot 'weights 'right)))
   :value
   (function/lam
    [['weights vector-type] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [start (dot 'weights 'left)
          commuted-left (dot 'left 'weights)
          commuted-right (dot 'right 'weights)
          finish (dot 'weights 'right)]
      (transitive
       start commuted-right finish
       (transitive
        start commuted-left commuted-right
        (app (function/const* 'vector/dot-commutative [])
             'weights 'left)
        (app
         (function/const* 'vector/dot-left-respects-equivalence [])
         'left 'right 'weights 'same))
       (app (function/const* 'vector/dot-commutative [])
            'right 'weights))))})

(def dot-respects-equivalence-spec
  {:name 'vector/dot-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (signed-equivalent
     (dot 'left 'right) (dot 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (transitive
     (dot 'left 'right)
     (dot 'left-prime 'right)
     (dot 'left-prime 'right-prime)
     (app (function/const* 'vector/dot-left-respects-equivalence [])
          'left 'left-prime 'right 'left-same)
     (app (function/const* 'vector/dot-right-respects-equivalence [])
          'left-prime 'right 'right-prime 'right-same)))})

(def definition-specs [])
(def theorem-specs
  [dot-left-respects-equivalence-spec
   dot-right-respects-equivalence-spec
   dot-respects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   checked-environment
   specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      subtract/extend-environment
      (extend-specs-if-missing
       :signed-multiply-ring signed-ring/theorem-specs)
      (support/extend-with :vector-dot-congruence theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
