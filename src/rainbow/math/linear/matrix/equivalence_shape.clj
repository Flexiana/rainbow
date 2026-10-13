(ns rainbow.math.linear.matrix.equivalence-shape
  "Shape transport for length-sensitive native matrix equivalence.

  Componentwise vector equivalence already forces equal list length, so it
  implies vector/same-shape.  Lifting that observation row-wise completes
  matrix/equivalent as an equivalence relation and proves that replacing a
  matrix by an equivalent one preserves compatibility and rectangularity.
  These are the transport laws required before shape-safe transpose and
  matrix composition can be exposed.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.equivalence :as equivalence]
            [rainbow.math.linear.matrix.shape :as matrix-shape]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.equivalence-laws :as vector-laws]
            [rainbow.math.linear.vector.equivalence-transitivity :as vector-transitivity]
            [rainbow.math.linear.vector.shape-cancellation :as vector-shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def truth (function/const* 'proposition/truth []))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- compatible [rows values]
  (app (function/const* 'matrix/compatible []) rows values))
(defn- rectangular [rows]
  (app (function/const* 'matrix/rectangular []) rows))
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

(def vector-equivalent-implies-same-shape-spec
  {:name 'vector/equivalent-implies-same-shape :universes []
   :type
   (function/forall
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (same-shape 'left 'right))
   :value
   (function/lam
    [['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (app
     (function/const* 'vector/map-respects-equivalence [])
     (function/lam [['ignored signed]] signed-zero)
     (function/lam
      [['left-component signed] ['right-component signed]
       ['component-same
        (app (function/const* 'signed/equivalent [])
             'left-component 'right-component)]]
      (app (function/const* 'signed/equivalent-reflexive []) signed-zero))
     'left 'right 'same))})

(def matrix-equivalent-transitive-spec
  {:name 'matrix/equivalent-transitive :universes []
   :type
   (function/forall
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-equivalent 'left 'middle)]
     ['middle-right (matrix-equivalent 'middle 'right)]]
    (matrix-equivalent 'left 'right))
   :value
   (function/lam
    [['left matrix-type] ['middle matrix-type] ['right matrix-type]
     ['left-middle (matrix-equivalent 'left 'middle)]
     ['middle-right (matrix-equivalent 'middle 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-middle matrix-type] ['current-right matrix-type]
             ['current-left-middle
              (matrix-equivalent 'current-left 'current-middle)]
             ['current-middle-right
              (matrix-equivalent 'current-middle 'current-right)]]
            (matrix-equivalent 'current-left 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                middle-motive
                (function/lam
                 [['current-middle matrix-type]]
                 (function/forall
                  [['current-right matrix-type]
                   ['current-left-middle
                    (matrix-equivalent empty 'current-middle)]
                   ['current-middle-right
                    (matrix-equivalent 'current-middle 'current-right)]]
                  (matrix-equivalent empty 'current-right)))]
            (function/lam
             [['current-middle matrix-type]]
             (matrix-rec
              middle-motive
              (function/lam
               [['current-right matrix-type]]
               (let [right-motive
                     (function/lam
                      [['candidate matrix-type]]
                      (function/forall
                       [['current-left-middle
                         (matrix-equivalent empty empty)]
                        ['current-middle-right
                         (matrix-equivalent empty 'candidate)]]
                       (matrix-equivalent empty 'candidate)))]
                 (matrix-rec
                  right-motive
                  (function/lam
                   [['current-left-middle (matrix-equivalent empty empty)]
                    ['current-middle-right (matrix-equivalent empty empty)]]
                   trivial)
                  (function/lam
                   [['right-row vector-type] ['right-tail matrix-type]
                    ['ignored (app right-motive 'right-tail)]]
                   (function/lam
                    [['current-left-middle (matrix-equivalent empty empty)]
                     ['current-middle-right
                      (matrix-equivalent
                       empty (cons-matrix 'right-row 'right-tail))]]
                    (absurd
                     (matrix-equivalent
                      empty (cons-matrix 'right-row 'right-tail))
                     'current-middle-right)))
                  'current-right)))
              (function/lam
               [['middle-row vector-type] ['middle-tail matrix-type]
                ['ignored (app middle-motive 'middle-tail)]]
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-equivalent
                   empty (cons-matrix 'middle-row 'middle-tail))]
                 ['current-middle-right
                  (matrix-equivalent
                   (cons-matrix 'middle-row 'middle-tail)
                   'current-right)]]
                (absurd
                 (matrix-equivalent empty 'current-right)
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
                     (matrix-equivalent current-left 'current-middle)]
                    ['current-middle-right
                     (matrix-equivalent 'current-middle 'current-right)]]
                   (matrix-equivalent current-left 'current-right)))]
             (function/lam
              [['current-middle matrix-type]]
              (matrix-rec
               middle-motive
               (function/lam
                [['current-right matrix-type]
                 ['current-left-middle
                  (matrix-equivalent current-left (nil-matrix))]
                 ['current-middle-right
                  (matrix-equivalent (nil-matrix) 'current-right)]]
                (absurd
                 (matrix-equivalent current-left 'current-right)
                 'current-left-middle))
               (function/lam
                [['middle-row vector-type] ['middle-tail matrix-type]
                 ['ignored-middle (app middle-motive 'middle-tail)]]
                (let [current-middle
                      (cons-matrix 'middle-row 'middle-tail)
                      right-motive
                      (function/lam
                       [['current-right matrix-type]]
                       (function/forall
                        [['current-left-middle
                          (matrix-equivalent current-left current-middle)]
                         ['current-middle-right
                          (matrix-equivalent current-middle 'current-right)]]
                        (matrix-equivalent current-left 'current-right)))]
                  (function/lam
                   [['current-right matrix-type]]
                   (matrix-rec
                    right-motive
                    (function/lam
                     [['current-left-middle
                       (matrix-equivalent current-left current-middle)]
                      ['current-middle-right
                       (matrix-equivalent current-middle (nil-matrix))]]
                     (absurd
                      (matrix-equivalent current-left (nil-matrix))
                      'current-middle-right))
                    (function/lam
                     [['right-row vector-type] ['right-tail matrix-type]
                      ['ignored-right (app right-motive 'right-tail)]]
                     (function/lam
                      [['current-left-middle
                        (matrix-equivalent current-left current-middle)]
                       ['current-middle-right
                        (matrix-equivalent
                         current-middle
                         (cons-matrix 'right-row 'right-tail))]]
                      (let [left-head-middle
                            (proposition-left
                             (vector-equivalent 'left-row 'middle-row)
                             (matrix-equivalent 'left-tail 'middle-tail)
                             'current-left-middle)
                            left-tail-middle
                            (proposition-right
                             (vector-equivalent 'left-row 'middle-row)
                             (matrix-equivalent 'left-tail 'middle-tail)
                             'current-left-middle)
                            middle-head-right
                            (proposition-left
                             (vector-equivalent 'middle-row 'right-row)
                             (matrix-equivalent 'middle-tail 'right-tail)
                             'current-middle-right)
                            middle-tail-right
                            (proposition-right
                             (vector-equivalent 'middle-row 'right-row)
                             (matrix-equivalent 'middle-tail 'right-tail)
                             'current-middle-right)]
                        (conjoin
                         (vector-equivalent 'left-row 'right-row)
                         (matrix-equivalent 'left-tail 'right-tail)
                         (app
                          (function/const* 'vector/equivalent-transitive [])
                          'left-row 'middle-row 'right-row
                          left-head-middle middle-head-right)
                         (app 'tail-transitive
                              'middle-tail 'right-tail
                              left-tail-middle middle-tail-right)))))
                    'current-right))))
               'current-middle))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'middle 'right 'left-middle 'middle-right)))})

(def equivalent-preserves-compatibility-spec
  {:name 'matrix/equivalent-preserves-compatibility :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['same (matrix-equivalent 'left 'right)]
     ['left-compatible (compatible 'left 'values)]]
    (compatible 'right 'values))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['same (matrix-equivalent 'left 'right)]
     ['left-compatible (compatible 'left 'values)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type] ['current-values vector-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]
             ['current-compatible
              (compatible 'current-left 'current-values)]]
            (compatible 'current-right 'current-values)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-values vector-type]
                   ['current-same
                    (matrix-equivalent empty 'current-right)]
                   ['current-compatible
                    (compatible empty 'current-values)]]
                  (compatible 'current-right 'current-values)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-values vector-type]
                ['current-same (matrix-equivalent empty empty)]
                ['current-compatible (compatible empty 'current-values)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-values vector-type]
                 ['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]
                 ['current-compatible (compatible empty 'current-values)]]
                (absurd
                 (compatible
                  (cons-matrix 'right-row 'right-tail) 'current-values)
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-preserves (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-values vector-type]
                    ['current-same
                     (matrix-equivalent current-left 'current-right)]
                    ['current-compatible
                     (compatible current-left 'current-values)]]
                   (compatible 'current-right 'current-values)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-values vector-type]
                 ['current-same
                  (matrix-equivalent current-left (nil-matrix))]
                 ['current-compatible
                  (compatible current-left 'current-values)]]
                (absurd
                 (compatible (nil-matrix) 'current-values)
                 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-values vector-type]
                  ['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]
                  ['current-compatible
                   (compatible current-left 'current-values)]]
                 (let [head-equivalent
                       (proposition-left
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-equivalent
                       (proposition-right
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       left-head-shape
                       (proposition-left
                        (same-shape 'left-row 'current-values)
                        (compatible 'left-tail 'current-values)
                        'current-compatible)
                       left-tail-compatible
                       (proposition-right
                        (same-shape 'left-row 'current-values)
                        (compatible 'left-tail 'current-values)
                        'current-compatible)
                       left-right-shape
                       (app
                        (function/const*
                         'vector/equivalent-implies-same-shape [])
                        'left-row 'right-row head-equivalent)
                       right-left-shape
                       (app (function/const* 'vector/same-shape-symmetric [])
                            'left-row 'right-row left-right-shape)
                       right-values-shape
                       (app (function/const* 'vector/same-shape-transitive [])
                            'right-row 'left-row 'current-values
                            right-left-shape left-head-shape)
                       right-tail-compatible
                       (app 'tail-preserves
                            'right-tail 'current-values
                            tail-equivalent left-tail-compatible)]
                   (conjoin
                    (same-shape 'right-row 'current-values)
                    (compatible 'right-tail 'current-values)
                    right-values-shape right-tail-compatible))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'values 'same 'left-compatible)))})

(def equivalent-preserves-rectangularity-spec
  {:name 'matrix/equivalent-preserves-rectangularity :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]
     ['left-rectangular (rectangular 'left)]]
    (rectangular 'right))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['same (matrix-equivalent 'left 'right)]
     ['left-rectangular (rectangular 'left)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-same
              (matrix-equivalent 'current-left 'current-right)]
             ['current-rectangular (rectangular 'current-left)]]
            (rectangular 'current-right)))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent empty 'current-right)]
                   ['current-rectangular (rectangular empty)]]
                  (rectangular 'current-right)))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]
                ['current-rectangular (rectangular empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'right-row 'right-tail))]
                 ['current-rectangular (rectangular empty)]]
                (absurd
                 (rectangular (cons-matrix 'right-row 'right-tail))
                 'current-same)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['ignored (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent current-left 'current-right)]
                    ['current-rectangular (rectangular current-left)]]
                   (rectangular 'current-right)))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]
                 ['current-rectangular (rectangular current-left)]]
                (absurd (rectangular (nil-matrix)) 'current-same))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored-right (app right-motive 'right-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'right-row 'right-tail))]
                  ['current-rectangular (rectangular current-left)]]
                 (let [head-equivalent
                       (proposition-left
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       tail-equivalent
                       (proposition-right
                        (vector-equivalent 'left-row 'right-row)
                        (matrix-equivalent 'left-tail 'right-tail)
                        'current-same)
                       row-shape
                       (app
                        (function/const*
                         'vector/equivalent-implies-same-shape [])
                        'left-row 'right-row head-equivalent)
                       left-tail-right-row
                       (app (function/const* 'matrix/compatible-transport [])
                            'left-tail 'left-row 'right-row
                            row-shape 'current-rectangular)]
                   (app
                    (function/const*
                     'matrix/equivalent-preserves-compatibility [])
                    'left-tail 'right-tail 'right-row
                    tail-equivalent left-tail-right-row))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'same 'left-rectangular)))})

(def definition-specs [])
(def theorem-specs
  [vector-equivalent-implies-same-shape-spec
   matrix-equivalent-transitive-spec
   equivalent-preserves-compatibility-spec
   equivalent-preserves-rectangularity-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      equivalence/extend-environment
      (extend-spec-if-missing
       'vector/map-respects-equivalence :vector-equivalence-laws
       vector-laws/map-respects-equivalence-spec)
      (extend-spec-if-missing
       'vector/equivalent-transitive :vector-equivalence-transitivity
       vector-transitivity/equivalent-transitive-spec)
      (extend-spec-if-missing
       'vector/same-shape :vector-shape-cancellation
       vector-shape/same-shape-spec)
      (extend-spec-if-missing
       'vector/same-shape-reflexive :vector-shape-cancellation
       vector-shape/same-shape-reflexive-spec)
      (extend-spec-if-missing
       'vector/same-shape-symmetric :vector-shape-cancellation
       vector-shape/same-shape-symmetric-spec)
      (extend-spec-if-missing
       'vector/same-shape-transitive :vector-shape-cancellation
       vector-shape/same-shape-transitive-spec)
      (extend-spec-if-missing
       'matrix/compatible :finite-matrix-shape
       matrix-shape/compatible-spec)
      (extend-spec-if-missing
       'matrix/rectangular :finite-matrix-shape
       matrix-shape/rectangular-spec)
      (extend-spec-if-missing
       'matrix/compatible-transport :finite-matrix-shape
       matrix-shape/compatible-transport-spec)
      (support/extend-with :finite-matrix-equivalence-shape theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
