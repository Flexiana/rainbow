(ns rainbow.math.linear.matrix.add-order
  "Pointwise order laws for native matrix addition and subtraction.

  Adding the same matrix preserves order; commutativity gives the mirrored law,
  and transitivity combines both varying arguments.  Since subtraction is
  addition of pointwise negation, it is monotone in its left argument, antitone
  in its right argument, and mixed monotone/antitone jointly.  Native and
  axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-antitone :as base]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.add-order :as vector-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
(defn- matrix-subtract [left right]
  (app (function/const* 'matrix/subtract []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- matrix-at-most [left right]
  (app (function/const* 'matrix/at-most []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def add-right-monotone-spec
  {:name 'matrix/add-right-monotone :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most
     (matrix-addition 'left 'offset)
     (matrix-addition 'right 'offset)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type] ['current-offset matrix-type]
             ['current-ordered
              (matrix-at-most 'current-left 'current-right)]]
            (matrix-at-most
             (matrix-addition 'current-left 'current-offset)
             (matrix-addition 'current-right 'current-offset))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-offset matrix-type]
                   ['current-ordered
                    (matrix-at-most empty 'current-right)]]
                  (matrix-at-most
                   (matrix-addition empty 'current-offset)
                   (matrix-addition 'current-right 'current-offset))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-offset matrix-type]
                ['current-ordered (matrix-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-offset matrix-type]
                 ['current-ordered
                  (matrix-at-most
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (matrix-at-most
                  (matrix-addition empty 'current-offset)
                  (matrix-addition
                   (cons-matrix 'right-row 'right-tail)
                   'current-offset))
                 'current-ordered)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-offset matrix-type]
                    ['current-ordered
                     (matrix-at-most current-left 'current-right)]]
                   (matrix-at-most
                    (matrix-addition current-left 'current-offset)
                    (matrix-addition 'current-right 'current-offset))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-offset matrix-type]
                 ['current-ordered
                  (matrix-at-most current-left (nil-matrix))]]
                (absurd
                 (matrix-at-most
                  (matrix-addition current-left 'current-offset)
                  (matrix-addition (nil-matrix) 'current-offset))
                 'current-ordered))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (let [current-right
                      (cons-matrix 'right-row 'right-tail)
                      offset-motive
                      (function/lam
                       [['current-offset matrix-type]]
                       (function/forall
                        [['current-ordered
                          (matrix-at-most current-left current-right)]]
                        (matrix-at-most
                         (matrix-addition current-left 'current-offset)
                         (matrix-addition current-right 'current-offset))))]
                  (function/lam
                   [['current-offset matrix-type]]
                   (matrix-rec
                    offset-motive
                    (function/lam
                     [['current-ordered
                       (matrix-at-most current-left current-right)]]
                     trivial)
                    (function/lam
                     [['offset-row vector-type] ['offset-tail matrix-type]
                      ['ignored (app offset-motive 'offset-tail)]]
                     (function/lam
                      [['current-ordered
                        (matrix-at-most current-left current-right)]]
                      (let [row-order
                            (vector-at-most 'left-row 'right-row)
                            tail-order
                            (matrix-at-most 'left-tail 'right-tail)]
                        (conjoin
                         (vector-at-most
                          (vector-add 'left-row 'offset-row)
                          (vector-add 'right-row 'offset-row))
                         (matrix-at-most
                          (matrix-addition 'left-tail 'offset-tail)
                          (matrix-addition 'right-tail 'offset-tail))
                         (app
                          (function/const* 'vector/add-right-monotone [])
                          'left-row 'right-row 'offset-row
                          (proposition-left
                           row-order tail-order 'current-ordered))
                         (app 'tail-monotone
                              'right-tail 'offset-tail
                              (proposition-right
                               row-order tail-order
                               'current-ordered))))))
                    'current-offset))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'offset 'ordered)))})

(def add-left-monotone-spec
  {:name 'matrix/add-left-monotone :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most
     (matrix-addition 'offset 'left)
     (matrix-addition 'offset 'right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['offset matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [source-left (matrix-addition 'left 'offset)
          source-right (matrix-addition 'right 'offset)
          target-left (matrix-addition 'offset 'left)
          target-right (matrix-addition 'offset 'right)
          source-order
          (app (function/const* 'matrix/add-right-monotone [])
               'left 'right 'offset 'ordered)]
      (app (function/const* 'matrix/at-most-respects-equivalence [])
           source-left target-left source-right target-right
           (app (function/const* 'matrix/add-commutative [])
                'left 'offset)
           (app (function/const* 'matrix/add-commutative [])
                'right 'offset)
           source-order)))})

(def add-monotone-spec
  {:name 'matrix/add-monotone :universes []
   :type
   (function/forall
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (matrix-at-most
     (matrix-addition 'left 'right)
     (matrix-addition 'left* 'right*)))
   :value
   (function/lam
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (app (function/const* 'matrix/at-most-transitive [])
         (matrix-addition 'left 'right)
         (matrix-addition 'left* 'right)
         (matrix-addition 'left* 'right*)
         (app (function/const* 'matrix/add-right-monotone [])
              'left 'left* 'right 'left-ordered)
         (app (function/const* 'matrix/add-left-monotone [])
              'right 'right* 'left* 'right-ordered)))})

(def subtract-left-monotone-spec
  {:name 'matrix/subtract-left-monotone :universes []
   :type
   (function/forall
    [['left matrix-type] ['left* matrix-type] ['right matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]]
    (matrix-at-most
     (matrix-subtract 'left 'right)
     (matrix-subtract 'left* 'right)))
   :value
   (function/lam
    [['left matrix-type] ['left* matrix-type] ['right matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]]
    (app (function/const* 'matrix/add-right-monotone [])
         'left 'left* (matrix-negate 'right) 'left-ordered))})

(def subtract-right-antitone-spec
  {:name 'matrix/subtract-right-antitone :universes []
   :type
   (function/forall
    [['right matrix-type] ['right* matrix-type] ['left matrix-type]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (matrix-at-most
     (matrix-subtract 'left 'right*)
     (matrix-subtract 'left 'right)))
   :value
   (function/lam
    [['right matrix-type] ['right* matrix-type] ['left matrix-type]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (app (function/const* 'matrix/add-left-monotone [])
         (matrix-negate 'right*) (matrix-negate 'right) 'left
         (app (function/const* 'matrix/negate-reverses-order [])
              'right 'right* 'right-ordered)))})

(def subtract-monotone-antitone-spec
  {:name 'matrix/subtract-monotone-antitone :universes []
   :type
   (function/forall
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (matrix-at-most
     (matrix-subtract 'left 'right*)
     (matrix-subtract 'left* 'right)))
   :value
   (function/lam
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-ordered (matrix-at-most 'left 'left*)]
     ['right-ordered (matrix-at-most 'right 'right*)]]
    (app (function/const* 'matrix/add-monotone [])
         'left 'left*
         (matrix-negate 'right*) (matrix-negate 'right)
         'left-ordered
         (app (function/const* 'matrix/negate-reverses-order [])
              'right 'right* 'right-ordered)))})

(def definition-specs [])
(def theorem-specs
  [add-right-monotone-spec
   add-left-monotone-spec
   add-monotone-spec
   subtract-left-monotone-spec
   subtract-right-antitone-spec
   subtract-monotone-antitone-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      base/extend-environment
      (extend-spec-if-missing
       'vector/add-right-monotone :vector-add-order
       vector-order/add-right-monotone-spec)
      (support/extend-with :finite-matrix-add-order theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
