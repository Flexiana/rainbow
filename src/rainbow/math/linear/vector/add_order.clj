(ns rainbow.math.linear.vector.add-order
  "Translation monotonicity for native signed vectors.

    left <= right  ->  left + offset <= right + offset

  All relations are `vector/at-most`, so the hypothesis carries equal dimension
  for left and right.  The fixed offset may have any length: vector/add truncates
  both results at the same point, preserving equal result dimensions and the
  componentwise order.  Impossible mismatched-input branches are eliminated
  from the order evidence.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.commutative :as commutative]
            [rainbow.math.rational.signed.add-associative :as associative]
            [rainbow.math.rational.signed.order-monotone :as signed-monotone]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
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
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def trivial (function/const* 'proposition/trivial []))

(def add-right-monotone-spec
  {:name 'vector/add-right-monotone :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-add 'left 'offset)
     (vector-add 'right 'offset)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type] ['current-offset vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-add 'current-left 'current-offset)
             (vector-add 'current-right 'current-offset))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-offset vector-type]
                   ['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (vector-add empty 'current-offset)
                   (vector-add 'current-right 'current-offset))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-offset vector-type]
                ['current-ordered (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-offset vector-type]
                 ['current-ordered
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (vector-at-most
                  (vector-add empty 'current-offset)
                  (vector-add
                   (cons-vector 'right-head 'right-tail) 'current-offset))
                 'current-ordered)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-offset vector-type]
                    ['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (vector-add current-left 'current-offset)
                    (vector-add 'current-right 'current-offset))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-offset vector-type]
                 ['current-ordered
                  (vector-at-most current-left (nil-vector))]]
                (absurd
                 (vector-at-most
                  (vector-add current-left 'current-offset)
                  (vector-add (nil-vector) 'current-offset))
                 'current-ordered))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (let [current-right (cons-vector 'right-head 'right-tail)
                      offset-motive
                      (function/lam
                       [['current-offset vector-type]]
                       (function/forall
                        [['current-ordered
                          (vector-at-most current-left current-right)]]
                        (vector-at-most
                         (vector-add current-left 'current-offset)
                         (vector-add current-right 'current-offset))))]
                  (function/lam
                   [['current-offset vector-type]]
                   (list-rec
                    offset-motive
                    (function/lam
                     [['current-ordered
                       (vector-at-most current-left current-right)]]
                     trivial)
                    (function/lam
                     [['offset-head signed] ['offset-tail vector-type]
                      ['ignored-offset (app offset-motive 'offset-tail)]]
                     (function/lam
                      [['current-ordered
                        (vector-at-most current-left current-right)]]
                      (let [head-order (at-most 'left-head 'right-head)
                            tail-order
                            (vector-at-most 'left-tail 'right-tail)]
                        (conjoin
                         (at-most
                          (signed-add 'left-head 'offset-head)
                          (signed-add 'right-head 'offset-head))
                         (vector-at-most
                          (vector-add 'left-tail 'offset-tail)
                          (vector-add 'right-tail 'offset-tail))
                         (app
                          (function/const* 'signed/add-right-monotone [])
                          'left-head 'right-head 'offset-head
                          (proposition-left
                           head-order tail-order 'current-ordered))
                         (app 'tail-monotone 'right-tail 'offset-tail
                              (proposition-right
                               head-order tail-order
                               'current-ordered))))))
                    'current-offset))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'offset 'ordered)))})

(def add-left-monotone-spec
  {:name 'vector/add-left-monotone :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-add 'offset 'left)
     (vector-add 'offset 'right)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type] ['offset vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (let [offset-motive
          (function/lam
           [['current-offset vector-type]]
           (function/forall
            [['current-left vector-type] ['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-add 'current-offset 'current-left)
             (vector-add 'current-offset 'current-right))))
          offset-base
          (function/lam
           [['current-left vector-type] ['current-right vector-type]
            ['current-ordered
             (vector-at-most 'current-left 'current-right)]]
           trivial)
          offset-step
          (function/lam
           [['offset-head signed] ['offset-tail vector-type]
            ['tail-monotone (app offset-motive 'offset-tail)]]
           (let [current-offset (cons-vector 'offset-head 'offset-tail)
                 left-motive
                 (function/lam
                  [['current-left vector-type]]
                  (function/forall
                   [['current-right vector-type]
                    ['current-ordered
                     (vector-at-most 'current-left 'current-right)]]
                   (vector-at-most
                    (vector-add current-offset 'current-left)
                    (vector-add current-offset 'current-right))))]
             (function/lam
              [['current-left vector-type]]
              (list-rec
               left-motive
               (let [empty (nil-vector)
                     right-motive
                     (function/lam
                      [['current-right vector-type]]
                      (function/forall
                       [['current-ordered
                         (vector-at-most empty 'current-right)]]
                       (vector-at-most
                        (vector-add current-offset empty)
                        (vector-add current-offset 'current-right))))]
                 (function/lam
                  [['current-right vector-type]]
                  (list-rec
                   right-motive
                   (function/lam
                    [['current-ordered (vector-at-most empty empty)]]
                    trivial)
                   (function/lam
                    [['right-head signed] ['right-tail vector-type]
                     ['ignored (app right-motive 'right-tail)]]
                    (function/lam
                     [['current-ordered
                       (vector-at-most
                        empty (cons-vector 'right-head 'right-tail))]]
                     (absurd
                      (vector-at-most
                       (vector-add current-offset empty)
                       (vector-add
                        current-offset
                        (cons-vector 'right-head 'right-tail)))
                      'current-ordered)))
                   'current-right)))
               (function/lam
                [['left-head signed] ['left-tail vector-type]
                 ['ignored (app left-motive 'left-tail)]]
                (let [current-left (cons-vector 'left-head 'left-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (function/forall
                        [['current-ordered
                          (vector-at-most current-left 'current-right)]]
                        (vector-at-most
                         (vector-add current-offset current-left)
                         (vector-add current-offset 'current-right))))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    (function/lam
                     [['current-ordered
                       (vector-at-most current-left (nil-vector))]]
                     (absurd
                      (vector-at-most
                       (vector-add current-offset current-left)
                       (vector-add current-offset (nil-vector)))
                      'current-ordered))
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-ordered
                        (vector-at-most
                         current-left
                         (cons-vector 'right-head 'right-tail))]]
                      (let [head-order (at-most 'left-head 'right-head)
                            tail-order
                            (vector-at-most 'left-tail 'right-tail)]
                        (conjoin
                         (at-most
                          (signed-add 'offset-head 'left-head)
                          (signed-add 'offset-head 'right-head))
                         (vector-at-most
                          (vector-add 'offset-tail 'left-tail)
                          (vector-add 'offset-tail 'right-tail))
                         (app
                          (function/const* 'signed/add-left-monotone [])
                          'left-head 'right-head 'offset-head
                          (proposition-left
                           head-order tail-order 'current-ordered))
                         (app 'tail-monotone 'left-tail 'right-tail
                              (proposition-right
                               head-order tail-order
                               'current-ordered))))))
                    'current-right))))
               'current-left))))]
      (app (list-rec offset-motive offset-base offset-step 'offset)
           'left 'right 'ordered)))})

(def add-monotone-spec
  {:name 'vector/add-monotone :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (vector-at-most
     (vector-add 'left 'right)
     (vector-add 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (app (function/const* 'vector/at-most-transitive [])
         (vector-add 'left 'right)
         (vector-add 'left-prime 'right)
         (vector-add 'left-prime 'right-prime)
         (app (function/const* 'vector/add-right-monotone [])
              'left 'left-prime 'right 'left-ordered)
         (app (function/const* 'vector/add-left-monotone [])
              'right 'right-prime 'left-prime 'right-ordered)))})

(def add-respects-equivalence-spec
  {:name 'vector/add-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (vector-equivalent
     (vector-add 'left 'right)
     (vector-add 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (let [left-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               'left 'left-prime 'left-same)
          right-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               'right 'right-prime 'right-same)
          left-forward
          (proposition-left
           (vector-at-most 'left 'left-prime)
           (vector-at-most 'left-prime 'left)
           left-bounds)
          left-backward
          (proposition-right
           (vector-at-most 'left 'left-prime)
           (vector-at-most 'left-prime 'left)
           left-bounds)
          right-forward
          (proposition-left
           (vector-at-most 'right 'right-prime)
           (vector-at-most 'right-prime 'right)
           right-bounds)
          right-backward
          (proposition-right
           (vector-at-most 'right 'right-prime)
           (vector-at-most 'right-prime 'right)
           right-bounds)
          forward
          (app (function/const* 'vector/add-monotone [])
               'left 'left-prime 'right 'right-prime
               left-forward right-forward)
          backward
          (app (function/const* 'vector/add-monotone [])
               'left-prime 'left 'right-prime 'right
               left-backward right-backward)]
      (app (function/const* 'vector/at-most-antisymmetric [])
           (vector-add 'left 'right)
           (vector-add 'left-prime 'right-prime)
           forward backward)))})

(def add-commutative-spec
  {:name 'vector/add-commutative :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-add 'left 'right)
     (vector-add 'right 'left)))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]]
    (let [motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (vector-equivalent
             (vector-add 'current-left 'current-right)
             (vector-add 'current-right 'current-left))))
          base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (vector-equivalent
                  (vector-add empty 'current-right)
                  (vector-add 'current-right empty)))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              trivial
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               trivial)
              'current-right)))
          step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-commutative (app motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (vector-equivalent
                   (vector-add current-left 'current-right)
                   (vector-add 'current-right current-left)))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               trivial
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (conjoin
                 (app (function/const* 'signed/equivalent [])
                      (signed-add 'left-head 'right-head)
                      (signed-add 'right-head 'left-head))
                 (vector-equivalent
                  (vector-add 'left-tail 'right-tail)
                  (vector-add 'right-tail 'left-tail))
                 (app (function/const* 'signed/add-commutative [])
                      'left-head 'right-head)
                 (app 'tail-commutative 'right-tail)))
               'current-right))))]
      (app (list-rec motive base step 'left) 'right)))})

(def add-associative-spec
  {:name 'vector/add-associative :universes []
   :type
   (function/forall
    [['left vector-type] ['middle vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-add (vector-add 'left 'middle) 'right)
     (vector-add 'left (vector-add 'middle 'right))))
   :value
   (function/lam
    [['left vector-type] ['middle vector-type] ['right vector-type]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-middle vector-type] ['current-right vector-type]]
            (vector-equivalent
             (vector-add
              (vector-add 'current-left 'current-middle)
              'current-right)
             (vector-add
              'current-left
              (vector-add 'current-middle 'current-right)))))
          outer-base
          (function/lam
           [['current-middle vector-type] ['current-right vector-type]]
           trivial)
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-associative (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle vector-type]]
                  (function/forall
                   [['current-right vector-type]]
                   (vector-equivalent
                    (vector-add
                     (vector-add current-left 'current-middle)
                     'current-right)
                    (vector-add
                     current-left
                     (vector-add 'current-middle 'current-right)))))]
             (function/lam
              [['current-middle vector-type]]
              (list-rec
               middle-motive
               (function/lam
                [['current-right vector-type]]
                trivial)
               (function/lam
                [['middle-head signed] ['middle-tail vector-type]
                 ['ignored-middle (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-vector 'middle-head 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right vector-type]]
                       (vector-equivalent
                        (vector-add
                         (vector-add current-left current-middle)
                         'current-right)
                        (vector-add
                         current-left
                         (vector-add current-middle 'current-right))))]
                  (function/lam
                   [['current-right vector-type]]
                   (list-rec
                    right-motive
                    trivial
                    (function/lam
                     [['right-head signed] ['right-tail vector-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (conjoin
                      (app (function/const* 'signed/equivalent [])
                           (signed-add
                            (signed-add 'left-head 'middle-head)
                            'right-head)
                           (signed-add
                            'left-head
                            (signed-add 'middle-head 'right-head)))
                      (vector-equivalent
                       (vector-add
                        (vector-add 'left-tail 'middle-tail)
                        'right-tail)
                       (vector-add
                        'left-tail
                        (vector-add 'middle-tail 'right-tail)))
                      (app (function/const* 'signed/add-associative [])
                           'left-head 'middle-head 'right-head)
                      (app 'tail-associative
                           'middle-tail 'right-tail)))
                    'current-right))))
               'current-middle))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'middle 'right)))})

(def definition-specs [])
(def theorem-specs
  [add-right-monotone-spec add-left-monotone-spec add-monotone-spec
   add-respects-equivalence-spec add-commutative-spec add-associative-spec])

(defn- extend-signed-monotone-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/add-right-monotone)
    checked-environment
    (support/extend-with checked-environment :signed-order-monotone
                         signed-monotone/theorem-specs)))

(defn- extend-signed-commutative-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/add-commutative)
    checked-environment
    (support/extend-with checked-environment :nnrat-commutative
                         [commutative/signed-add-commutative-spec])))

(defn- extend-signed-associative-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/add-associative)
    checked-environment
    (support/extend-with checked-environment :signed-add-associative
                         [associative/add-associative-spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-signed-monotone-if-missing extend-signed-commutative-if-missing extend-signed-associative-if-missing (support/extend-with :vector-add-order theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.add-order))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
