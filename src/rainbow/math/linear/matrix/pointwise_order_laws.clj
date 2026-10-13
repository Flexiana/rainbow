(ns rainbow.math.linear.matrix.pointwise-order-laws
  "Partial-order and quotient-transport laws for native finite matrices.

  Matrix pointwise order is transitive, reversed by pointwise negation, and
  antisymmetric up to length-sensitive matrix equivalence.  Matrix equivalence
  yields both order directions, and order endpoints may therefore be replaced
  by equivalent representatives.  Dimension mismatches eliminate through the
  falsity branches of the reducible relation.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.signed-scale-order :as order]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.pointwise-order-laws :as vector-laws]))

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
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- matrix-at-most [left right]
  (app (function/const* 'matrix/at-most []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- matrix-negate [rows]
  (app (function/const* 'matrix/negate []) rows))
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

(def negate-reverses-order-spec
  {:name 'matrix/negate-reverses-order :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most
     (matrix-negate 'right)
     (matrix-negate 'left)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-ordered
              (matrix-at-most 'current-left 'current-right)]]
            (matrix-at-most
             (matrix-negate 'current-right)
             (matrix-negate 'current-left))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-ordered
                    (matrix-at-most empty 'current-right)]]
                  (matrix-at-most
                   (matrix-negate 'current-right)
                   (matrix-negate empty))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-ordered (matrix-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (matrix-at-most
                   empty (cons-matrix 'right-row 'right-tail))]]
                'current-ordered))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-reverses (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-ordered
                     (matrix-at-most current-left 'current-right)]]
                   (matrix-at-most
                    (matrix-negate 'current-right)
                    (matrix-negate current-left))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-ordered
                  (matrix-at-most current-left (nil-matrix))]]
                'current-ordered)
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (matrix-at-most
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [row-order (vector-at-most 'left-row 'right-row)
                       tail-order (matrix-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (vector-at-most
                     (vector-negate 'right-row)
                     (vector-negate 'left-row))
                    (matrix-at-most
                     (matrix-negate 'right-tail)
                     (matrix-negate 'left-tail))
                    (app (function/const* 'vector/negate-reverses-order [])
                         'left-row 'right-row
                         (proposition-left
                          row-order tail-order 'current-ordered))
                    (app 'tail-reverses 'right-tail
                         (proposition-right
                          row-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def at-most-transitive-spec
  {:name 'matrix/at-most-transitive :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-at-most 'left 'middle)]
     ['middle-right (matrix-at-most 'middle 'right)]]
    (matrix-at-most 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-at-most 'left 'middle)]
     ['middle-right (matrix-at-most 'middle 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-middle matrix-type] ['current-right matrix-type]
             ['current-left-middle
              (matrix-at-most 'current-left 'current-middle)]
             ['current-middle-right
              (matrix-at-most 'current-middle 'current-right)]]
            (matrix-at-most 'current-left 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                middle-motive
                (function/lam
                 [['current-middle matrix-type]]
                 (function/forall
                  [['current-right matrix-type]
                   ['current-left-middle
                    (matrix-at-most empty 'current-middle)]
                   ['current-middle-right
                    (matrix-at-most 'current-middle 'current-right)]]
                  (matrix-at-most empty 'current-right)))]
            (function/lam
             [['current-middle matrix-type]]
             (matrix-rec
              middle-motive
              (function/lam
               [['current-right matrix-type]]
               (let [right-motive
                     (function/lam
                      [['final-right matrix-type]]
                      (function/forall
                       [['current-left-middle
                         (matrix-at-most empty empty)]
                        ['current-middle-right
                         (matrix-at-most empty 'final-right)]]
                       (matrix-at-most empty 'final-right)))]
                 (matrix-rec
                  right-motive
                  (function/lam
                   [['current-left-middle (matrix-at-most empty empty)]
                    ['current-middle-right (matrix-at-most empty empty)]]
                   trivial)
                  (function/lam
                   [['right-row vector-type] ['right-tail matrix-type]
                    ['ignored (app right-motive 'right-tail)]]
                   (function/lam
                    [['current-left-middle (matrix-at-most empty empty)]
                     ['current-middle-right
                      (matrix-at-most
                       empty (cons-matrix 'right-row 'right-tail))]]
                    'current-middle-right))
                  'current-right)))
              (function/lam
               [['middle-row vector-type] ['middle-tail matrix-type]
                ['ignored (app middle-motive 'middle-tail)]]
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-at-most
                   empty (cons-matrix 'middle-row 'middle-tail))]
                 ['current-middle-right
                  (matrix-at-most
                   (cons-matrix 'middle-row 'middle-tail) 'current-right)]]
                (absurd (matrix-at-most empty 'current-right)
                        'current-left-middle)))
              'current-middle)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-transitive (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 middle-motive
                 (function/lam
                  [['current-middle matrix-type]]
                  (function/forall
                   [['current-right matrix-type]
                    ['current-left-middle
                     (matrix-at-most current-left 'current-middle)]
                    ['current-middle-right
                     (matrix-at-most 'current-middle 'current-right)]]
                   (matrix-at-most current-left 'current-right)))]
             (function/lam
              [['current-middle matrix-type]]
              (matrix-rec
               middle-motive
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-at-most current-left (nil-matrix))]
                 ['current-middle-right
                  (matrix-at-most (nil-matrix) 'current-right)]]
                (absurd (matrix-at-most current-left 'current-right)
                        'current-left-middle))
               (function/lam
                [['middle-row vector-type] ['middle-tail matrix-type]
                 ['ignored (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-matrix 'middle-row 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right matrix-type]]
                       (function/forall
                        [['current-left-middle
                          (matrix-at-most current-left current-middle)]
                         ['current-middle-right
                          (matrix-at-most current-middle 'current-right)]]
                        (matrix-at-most current-left 'current-right)))]
                  (function/lam
                   [['current-right matrix-type]]
                   (matrix-rec
                    right-motive
                    (function/lam
                     [['current-left-middle
                       (matrix-at-most current-left current-middle)]
                      ['current-middle-right
                       (matrix-at-most current-middle (nil-matrix))]]
                     'current-middle-right)
                    (function/lam
                     [['right-row vector-type] ['right-tail matrix-type]
                      ['ignored (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-left-middle
                        (matrix-at-most current-left current-middle)]
                       ['current-middle-right
                        (matrix-at-most
                         current-middle
                         (cons-matrix 'right-row 'right-tail))]]
                      (let [left-row-order
                            (proposition-left
                             (vector-at-most 'left-row 'middle-row)
                             (matrix-at-most 'left-tail 'middle-tail)
                             'current-left-middle)
                            left-tail-order
                            (proposition-right
                             (vector-at-most 'left-row 'middle-row)
                             (matrix-at-most 'left-tail 'middle-tail)
                             'current-left-middle)
                            right-row-order
                            (proposition-left
                             (vector-at-most 'middle-row 'right-row)
                             (matrix-at-most 'middle-tail 'right-tail)
                             'current-middle-right)
                            right-tail-order
                            (proposition-right
                             (vector-at-most 'middle-row 'right-row)
                             (matrix-at-most 'middle-tail 'right-tail)
                             'current-middle-right)]
                        (conjoin
                         (vector-at-most 'left-row 'right-row)
                         (matrix-at-most 'left-tail 'right-tail)
                         (app
                          (function/const* 'vector/at-most-transitive [])
                          'left-row 'middle-row 'right-row
                          left-row-order right-row-order)
                         (app 'tail-transitive
                              'middle-tail 'right-tail
                              left-tail-order right-tail-order)))))
                    'current-right))))
               'current-middle))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'middle 'right 'left-middle 'middle-right)))})

(def at-most-antisymmetric-spec
  {:name 'matrix/at-most-antisymmetric :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['left-right (matrix-at-most 'left 'right)]
     ['right-left (matrix-at-most 'right 'left)]]
    (matrix-equivalent 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['left-right (matrix-at-most 'left 'right)]
     ['right-left (matrix-at-most 'right 'left)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-left-right
              (matrix-at-most 'current-left 'current-right)]
             ['current-right-left
              (matrix-at-most 'current-right 'current-left)]]
            (matrix-equivalent 'current-left 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-left-right
                    (matrix-at-most empty 'current-right)]
                   ['current-right-left
                    (matrix-at-most 'current-right empty)]]
                  (matrix-equivalent empty 'current-right)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-left-right (matrix-at-most empty empty)]
                ['current-right-left (matrix-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-left-right
                  (matrix-at-most
                   empty (cons-matrix 'right-row 'right-tail))]
                 ['current-right-left
                  (matrix-at-most
                   (cons-matrix 'right-row 'right-tail) empty)]]
                (absurd
                 (matrix-equivalent
                  empty (cons-matrix 'right-row 'right-tail))
                 'current-left-right)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-antisymmetric (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-left-right
                     (matrix-at-most current-left 'current-right)]
                    ['current-right-left
                     (matrix-at-most 'current-right current-left)]]
                   (matrix-equivalent current-left 'current-right)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-left-right
                  (matrix-at-most current-left (nil-matrix))]
                 ['current-right-left
                  (matrix-at-most (nil-matrix) current-left)]]
                (absurd
                 (matrix-equivalent current-left (nil-matrix))
                 'current-left-right))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-left-right
                   (matrix-at-most
                    current-left
                    (cons-matrix 'right-row 'right-tail))]
                  ['current-right-left
                   (matrix-at-most
                    (cons-matrix 'right-row 'right-tail)
                    current-left)]]
                 (let [forward-row
                       (proposition-left
                        (vector-at-most 'left-row 'right-row)
                        (matrix-at-most 'left-tail 'right-tail)
                        'current-left-right)
                       forward-tail
                       (proposition-right
                        (vector-at-most 'left-row 'right-row)
                        (matrix-at-most 'left-tail 'right-tail)
                        'current-left-right)
                       backward-row
                       (proposition-left
                        (vector-at-most 'right-row 'left-row)
                        (matrix-at-most 'right-tail 'left-tail)
                        'current-right-left)
                       backward-tail
                       (proposition-right
                        (vector-at-most 'right-row 'left-row)
                        (matrix-at-most 'right-tail 'left-tail)
                        'current-right-left)]
                   (conjoin
                    (vector-equivalent 'left-row 'right-row)
                    (matrix-equivalent 'left-tail 'right-tail)
                    (app (function/const* 'vector/at-most-antisymmetric [])
                         'left-row 'right-row
                         forward-row backward-row)
                    (app 'tail-antisymmetric 'right-tail
                         forward-tail backward-tail)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'left-right 'right-left)))})

(def equivalent-to-mutual-at-most-spec
  {:name 'matrix/equivalent-to-mutual-at-most :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (conjunction
     (matrix-at-most 'left 'right)
     (matrix-at-most 'right 'left)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]]
            (conjunction
             (matrix-at-most 'current-left 'current-right)
             (matrix-at-most 'current-right 'current-left))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]]
                  (conjunction
                   (matrix-at-most empty 'current-right)
                   (matrix-at-most 'current-right empty))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               (conjoin
                (matrix-at-most empty empty)
                (matrix-at-most empty empty)
                trivial trivial))
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (conjunction
                  (matrix-at-most
                   empty (cons-matrix 'right-row 'right-tail))
                  (matrix-at-most
                   (cons-matrix 'right-row 'right-tail) empty))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-bounds (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]]
                   (conjunction
                    (matrix-at-most current-left 'current-right)
                    (matrix-at-most 'current-right current-left))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (conjunction
                  (matrix-at-most current-left (nil-matrix))
                  (matrix-at-most (nil-matrix) current-left))
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [row-same
                       (proposition-left
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       row-bounds
                       (app
                        (function/const*
                         'vector/equivalent-to-mutual-at-most [])
                        'left-row 'right-row row-same)
                       tail-result
                       (app 'tail-bounds 'right-tail tail-same)
                       row-forward
                       (proposition-left
                        (vector-at-most 'left-row 'right-row)
                        (vector-at-most 'right-row 'left-row)
                        row-bounds)
                       row-backward
                       (proposition-right
                        (vector-at-most 'left-row 'right-row)
                        (vector-at-most 'right-row 'left-row)
                        row-bounds)
                       tail-forward
                       (proposition-left
                        (matrix-at-most 'left-tail 'right-tail)
                        (matrix-at-most 'right-tail 'left-tail)
                        tail-result)
                       tail-backward
                       (proposition-right
                        (matrix-at-most 'left-tail 'right-tail)
                        (matrix-at-most 'right-tail 'left-tail)
                        tail-result)]
                   (conjoin
                    (matrix-at-most
                     current-left
                     (cons-matrix 'right-row 'right-tail))
                    (matrix-at-most
                     (cons-matrix 'right-row 'right-tail)
                     current-left)
                    (conjoin
                     (vector-at-most 'left-row 'right-row)
                     (matrix-at-most 'left-tail 'right-tail)
                     row-forward tail-forward)
                    (conjoin
                     (vector-at-most 'right-row 'left-row)
                     (matrix-at-most 'right-tail 'left-tail)
                     row-backward tail-backward)))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same)))})

(def equivalent-to-at-most-spec
  {:name 'matrix/equivalent-to-at-most :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (matrix-at-most 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]]
    (proposition-left
     (matrix-at-most 'left 'right)
     (matrix-at-most 'right 'left)
     (app (function/const* 'matrix/equivalent-to-mutual-at-most [])
          'left 'right 'same)))})

(def at-most-respects-equivalence-spec
  {:name 'matrix/at-most-respects-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-same (matrix-equivalent 'left 'left*)]
     ['right-same (matrix-equivalent 'right 'right*)]
     ['ordered (matrix-at-most 'left 'right)]]
    (matrix-at-most 'left* 'right*))
   :value
   (function/lam
    [['left matrix-type] ['left* matrix-type]
     ['right matrix-type] ['right* matrix-type]
     ['left-same (matrix-equivalent 'left 'left*)]
     ['right-same (matrix-equivalent 'right 'right*)]
     ['ordered (matrix-at-most 'left 'right)]]
    (let [left-bounds
          (app (function/const* 'matrix/equivalent-to-mutual-at-most [])
               'left 'left* 'left-same)
          right-bounds
          (app (function/const* 'matrix/equivalent-to-mutual-at-most [])
               'right 'right* 'right-same)
          left*-left
          (proposition-right
           (matrix-at-most 'left 'left*)
           (matrix-at-most 'left* 'left)
           left-bounds)
          right-right*
          (proposition-left
           (matrix-at-most 'right 'right*)
           (matrix-at-most 'right* 'right)
           right-bounds)
          left*-right
          (app (function/const* 'matrix/at-most-transitive [])
               'left* 'left 'right left*-left 'ordered)]
      (app (function/const* 'matrix/at-most-transitive [])
           'left* 'right 'right* left*-right right-right*)))})

(def definition-specs [])
(def theorem-specs
  [negate-reverses-order-spec
   at-most-transitive-spec
   at-most-antisymmetric-spec
   equivalent-to-mutual-at-most-spec
   equivalent-to-at-most-spec
   at-most-respects-equivalence-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.signed-scale-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'vector/negate-reverses-order :vector-pointwise-order-laws vector-laws/negate-reverses-order-spec) (extend-spec-if-missing 'vector/at-most-transitive :vector-pointwise-order-laws vector-laws/at-most-transitive-spec) (extend-spec-if-missing 'vector/at-most-antisymmetric :vector-pointwise-order-laws vector-laws/at-most-antisymmetric-spec) (extend-spec-if-missing 'vector/equivalent-to-mutual-at-most :vector-pointwise-order-laws vector-laws/equivalent-to-mutual-at-most-spec) (support/extend-with :finite-matrix-pointwise-order-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.pointwise-order-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
