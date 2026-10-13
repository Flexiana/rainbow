(ns rainbow.math.linear.matrix.add
  "Length-sensitive shape, addition, and left distributivity for matrices.

  matrix/same-shape requires the same row count and the same length for each
  corresponding row.  matrix/add zips rows with the existing truncating vector
  addition.  The shape premise is exactly what makes native matrix action
  additive in its rows and matrix multiplication distributive in its left
  factor under total list semantics.  Native and axiom-free on D63."
  (:require [rainbow.math.linear.matrix.signed-scale-right :as bilinear]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def truth (function/const* 'proposition/truth []))
(def falsity (function/const* 'proposition/falsity []))
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
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- matrix-add [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
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

(def same-shape-spec
  {:name 'matrix/same-shape :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type 'Prop)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      vector-type
      (function/lam
       [['ignored matrix-type]]
       (function/arrow matrix-type 'Prop))
      (function/lam
       [['other matrix-type]]
       (app
        (function/const* 'data/List.rec [type-level type-level])
        vector-type
        (function/lam [['ignored matrix-type]] 'Prop)
        truth
        (function/lam
         [['other-row vector-type] ['other-tail matrix-type]
          ['ignored 'Prop]]
         falsity)
        'other))
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['recur (function/arrow matrix-type 'Prop)]]
       (function/lam
        [['other matrix-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         vector-type
         (function/lam [['ignored matrix-type]] 'Prop)
         falsity
         (function/lam
          [['other-row vector-type] ['other-tail matrix-type]
           ['ignored 'Prop]]
          (conjunction
           (vector-same-shape 'row 'other-row)
           (app 'recur 'other-tail)))
         'other)))
      'left)
     'right))})

(def add-spec
  {:name 'matrix/add :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type matrix-type)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (app
     (app
      (function/const* 'data/List.rec [type-level type-level])
      vector-type
      (function/lam
       [['ignored matrix-type]]
       (function/arrow matrix-type matrix-type))
      (function/lam
       [['ignored-right matrix-type]]
       (nil-matrix))
      (function/lam
       [['row vector-type] ['tail matrix-type]
        ['add-tail (function/arrow matrix-type matrix-type)]]
       (function/lam
        [['current-right matrix-type]]
        (app
         (function/const* 'data/List.rec [type-level type-level])
         vector-type
         (function/lam [['ignored matrix-type]] matrix-type)
         (nil-matrix)
         (function/lam
          [['right-row vector-type] ['right-tail matrix-type]
           ['ignored matrix-type]]
          (cons-matrix
           (vector-add 'row 'right-row)
           (app 'add-tail 'right-tail)))
         'current-right)))
      'left)
     'right))})

(def same-shape-reflexive-spec
  {:name 'matrix/same-shape-reflexive :universes []
   :type
   (function/forall
    [['rows matrix-type]]
    (matrix-same-shape 'rows 'rows))
   :value
   (function/lam
    [['rows matrix-type]]
    (let [motive
          (function/lam
           [['current matrix-type]]
           (matrix-same-shape 'current 'current))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-reflexive (app motive 'tail)]]
           (conjoin
            (vector-same-shape 'row 'row)
            (matrix-same-shape 'tail 'tail)
            (app (function/const* 'vector/same-shape-reflexive []) 'row)
            'tail-reflexive))]
      (matrix-rec motive trivial step 'rows)))})

(def vector-multiply-additive-rows-spec
  {:name 'matrix/vector-multiply-additive-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (vector-equivalent
     (vector-multiply (matrix-add 'left 'right) 'values)
     (vector-add
      (vector-multiply 'left 'values)
      (vector-multiply 'right 'values))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['values vector-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-shape
              (matrix-same-shape 'current-left 'current-right)]]
            (vector-equivalent
             (vector-multiply
              (matrix-add 'current-left 'current-right) 'values)
             (vector-add
              (vector-multiply 'current-left 'values)
              (vector-multiply 'current-right 'values)))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-shape
                    (matrix-same-shape empty 'current-right)]]
                  (vector-equivalent
                   (vector-multiply
                    (matrix-add empty 'current-right) 'values)
                   (vector-add
                    (vector-multiply empty 'values)
                    (vector-multiply 'current-right 'values)))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-shape (matrix-same-shape empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-shape
                  (matrix-same-shape
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (vector-equivalent
                  (vector-multiply
                   (matrix-add
                    empty (cons-matrix 'right-row 'right-tail))
                   'values)
                  (vector-add
                   (vector-multiply empty 'values)
                   (vector-multiply
                    (cons-matrix 'right-row 'right-tail) 'values)))
                 'current-shape)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-additive (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-shape
                     (matrix-same-shape current-left 'current-right)]]
                   (vector-equivalent
                    (vector-multiply
                     (matrix-add current-left 'current-right) 'values)
                    (vector-add
                     (vector-multiply current-left 'values)
                     (vector-multiply 'current-right 'values)))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-shape
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (vector-equivalent
                  (vector-multiply
                   (matrix-add current-left (nil-matrix)) 'values)
                  (vector-add
                   (vector-multiply current-left 'values)
                   (vector-multiply (nil-matrix) 'values)))
                 'current-shape))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-shape
                   (matrix-same-shape
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-shape
                       (vector-same-shape 'left-row 'right-row)
                       tail-shape
                       (matrix-same-shape 'left-tail 'right-tail)]
                   (conjoin
                    (signed-equivalent
                     (dot (vector-add 'left-row 'right-row) 'values)
                     (app (function/const* 'signed/add [])
                          (dot 'left-row 'values)
                          (dot 'right-row 'values)))
                    (vector-equivalent
                     (vector-multiply
                      (matrix-add 'left-tail 'right-tail) 'values)
                     (vector-add
                      (vector-multiply 'left-tail 'values)
                      (vector-multiply 'right-tail 'values)))
                    (app (function/const* 'vector/dot-additive-left [])
                         'left-row 'right-row 'values
                         (proposition-left
                          head-shape tail-shape 'current-shape))
                    (app 'tail-additive 'right-tail
                         (proposition-right
                          head-shape tail-shape 'current-shape))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'shape)))})

(def multiply-additive-left-spec
  {:name 'matrix/multiply-additive-left :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (multiply (matrix-add 'left 'right) 'factor)
     (matrix-add
      (multiply 'left 'factor)
      (multiply 'right 'factor))))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type] ['factor matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [factor-columns (transpose 'factor)
          outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-shape
              (matrix-same-shape 'current-left 'current-right)]]
            (matrix-equivalent
             (multiply
              (matrix-add 'current-left 'current-right) 'factor)
             (matrix-add
              (multiply 'current-left 'factor)
              (multiply 'current-right 'factor)))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-shape
                    (matrix-same-shape empty 'current-right)]]
                  (matrix-equivalent
                   (multiply
                    (matrix-add empty 'current-right) 'factor)
                   (matrix-add
                    (multiply empty 'factor)
                    (multiply 'current-right 'factor)))))]
            (function/lam
             [['current-right matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-shape (matrix-same-shape empty empty)]]
               trivial)
              (function/lam
               [['right-row vector-type] ['right-tail matrix-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-shape
                  (matrix-same-shape
                   empty (cons-matrix 'right-row 'right-tail))]]
                (absurd
                 (matrix-equivalent
                  (multiply
                   (matrix-add
                    empty (cons-matrix 'right-row 'right-tail))
                   'factor)
                  (matrix-add
                   (multiply empty 'factor)
                   (multiply
                    (cons-matrix 'right-row 'right-tail) 'factor)))
                 'current-shape)))
              'current-right)))
          outer-step
          (function/lam
           [['left-row vector-type] ['left-tail matrix-type]
            ['tail-distributes (app outer-motive 'left-tail)]]
           (let [current-left (cons-matrix 'left-row 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right matrix-type]]
                  (function/forall
                   [['current-shape
                     (matrix-same-shape current-left 'current-right)]]
                   (matrix-equivalent
                    (multiply
                     (matrix-add current-left 'current-right) 'factor)
                    (matrix-add
                     (multiply current-left 'factor)
                     (multiply 'current-right 'factor)))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-shape
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (multiply
                   (matrix-add current-left (nil-matrix)) 'factor)
                  (matrix-add
                   (multiply current-left 'factor)
                   (multiply (nil-matrix) 'factor)))
                 'current-shape))
               (function/lam
                [['right-row vector-type] ['right-tail matrix-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-shape
                   (matrix-same-shape
                    current-left
                    (cons-matrix 'right-row 'right-tail))]]
                 (let [head-shape
                       (vector-same-shape 'left-row 'right-row)
                       tail-shape
                       (matrix-same-shape 'left-tail 'right-tail)]
                   (conjoin
                    (vector-equivalent
                     (vector-multiply
                      factor-columns
                      (vector-add 'left-row 'right-row))
                     (vector-add
                      (vector-multiply factor-columns 'left-row)
                      (vector-multiply factor-columns 'right-row)))
                    (matrix-equivalent
                     (multiply
                      (matrix-add 'left-tail 'right-tail) 'factor)
                     (matrix-add
                      (multiply 'left-tail 'factor)
                      (multiply 'right-tail 'factor)))
                    (app
                     (function/const* 'matrix/vector-multiply-additive [])
                     factor-columns 'left-row 'right-row
                     (proposition-left
                      head-shape tail-shape 'current-shape))
                    (app 'tail-distributes 'right-tail
                         (proposition-right
                          head-shape tail-shape 'current-shape))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'shape)))})

(def definition-specs [same-shape-spec add-spec])
(def theorem-specs
  [same-shape-reflexive-spec
   vector-multiply-additive-rows-spec
   multiply-additive-left-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      bilinear/extend-environment
      (support/extend-with :finite-matrix-add
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
