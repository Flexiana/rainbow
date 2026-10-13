(ns rainbow.math.linear.matrix.signed-scale-algebra
  "Additivity and composition of arbitrary signed matrix scaling.

  The scale-difference representation is additive in its value and composes by
  signed multiplication.  Structural lifts give the corresponding laws for
  vector/signed-scale and matrix/signed-scale.  Additivity carries the exact
  length-sensitive shape premise required by truncating addition; composition
  is unrestricted.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.subtract-linear :as subtract-linear]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-associative :as associative]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level]) vector-type row tail))
(defn- vector-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- matrix-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- scalar-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- matrix-addition [left right]
  (app (function/const* 'matrix/add []) left right))
(defn- vector-signed-scale [factor values]
  (app (function/const* 'vector/signed-scale []) factor values))
(defn- matrix-signed-scale [factor rows]
  (app (function/const* 'matrix/signed-scale []) factor rows))
(defn- vector-same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- matrix-same-shape [left right]
  (app (function/const* 'matrix/same-shape []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- scale-difference [factor value]
  (signed-subtract
   (scalar-scale (positive factor) value)
   (scalar-scale (negative factor) value)))
(defn- signed-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- signed-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def scale-difference-additive-spec
  {:name 'signed/scale-difference-additive :universes []
   :type
   (function/forall
    [['factor signed] ['left signed] ['right signed]]
    (signed-equivalent
     (scale-difference 'factor (signed-add 'left 'right))
     (signed-add
      (scale-difference 'factor 'left)
      (scale-difference 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left signed] ['right signed]]
    (let [sum (signed-add 'left 'right)
          start (scale-difference 'factor sum)
          product (signed-multiply 'factor sum)
          split
          (signed-add
           (signed-multiply 'factor 'left)
           (signed-multiply 'factor 'right))
          finish
          (signed-add
           (scale-difference 'factor 'left)
           (scale-difference 'factor 'right))]
      (signed-transitive
       start split finish
       (signed-transitive
        start product split
        (app (function/const* 'signed/scale-difference-multiply [])
             'factor sum)
        (app (function/const* 'signed/multiply-distributes-add-left [])
             'factor 'left 'right))
       (app (function/const* 'signed/add-respects-equivalence [])
            (signed-multiply 'factor 'left)
            (scale-difference 'factor 'left)
            (signed-multiply 'factor 'right)
            (scale-difference 'factor 'right)
            (signed-symmetric
             (scale-difference 'factor 'left)
             (signed-multiply 'factor 'left)
             (app
              (function/const* 'signed/scale-difference-multiply [])
              'factor 'left))
            (signed-symmetric
             (scale-difference 'factor 'right)
             (signed-multiply 'factor 'right)
             (app
              (function/const* 'signed/scale-difference-multiply [])
              'factor 'right))))))})

(def scale-difference-compose-spec
  {:name 'signed/scale-difference-compose :universes []
   :type
   (function/forall
    [['outer signed] ['inner signed] ['value signed]]
    (signed-equivalent
     (scale-difference
      'outer (scale-difference 'inner 'value))
     (scale-difference
      (signed-multiply 'outer 'inner) 'value)))
   :value
   (function/lam
    [['outer signed] ['inner signed] ['value signed]]
    (let [inner-difference (scale-difference 'inner 'value)
          inner-product (signed-multiply 'inner 'value)
          factor-product (signed-multiply 'outer 'inner)
          start (scale-difference 'outer inner-difference)
          outer-inner-difference
          (signed-multiply 'outer inner-difference)
          right-nested (signed-multiply 'outer inner-product)
          left-nested (signed-multiply factor-product 'value)
          finish (scale-difference factor-product 'value)]
      (signed-transitive
       start right-nested finish
       (signed-transitive
        start outer-inner-difference right-nested
        (app (function/const* 'signed/scale-difference-multiply [])
             'outer inner-difference)
        (app
         (function/const* 'signed/multiply-left-respects-equivalence [])
         inner-difference inner-product 'outer
         (app (function/const* 'signed/scale-difference-multiply [])
              'inner 'value)))
       (signed-transitive
        right-nested left-nested finish
        (signed-symmetric
         left-nested right-nested
         (app (function/const* 'signed/multiply-associative [])
              'outer 'inner 'value))
        (signed-symmetric
         finish left-nested
         (app (function/const* 'signed/scale-difference-multiply [])
              factor-product 'value))))))})

(def vector-signed-scale-additive-spec
  {:name 'vector/signed-scale-additive :universes []
   :type
   (function/forall
    [['factor signed] ['left vector-type] ['right vector-type]
     ['shape (vector-same-shape 'left 'right)]]
    (vector-equivalent
     (vector-signed-scale 'factor (vector-add 'left 'right))
     (vector-add
      (vector-signed-scale 'factor 'left)
      (vector-signed-scale 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left vector-type] ['right vector-type]
     ['shape (vector-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-shape
              (vector-same-shape 'current-left 'current-right)]]
            (vector-equivalent
             (vector-signed-scale
              'factor (vector-add 'current-left 'current-right))
             (vector-add
              (vector-signed-scale 'factor 'current-left)
              (vector-signed-scale 'factor 'current-right)))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-shape
                    (vector-same-shape empty 'current-right)]]
                  (vector-equivalent
                   (vector-signed-scale
                    'factor (vector-add empty 'current-right))
                   (vector-add
                    (vector-signed-scale 'factor empty)
                    (vector-signed-scale
                     'factor 'current-right)))))]
            (function/lam
             [['current-right vector-type]]
             (vector-rec
              right-motive
              (function/lam
               [['current-shape (vector-same-shape empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-shape
                  (vector-same-shape
                   empty (cons-vector 'right-head 'right-tail))]]
                (absurd
                 (vector-equivalent
                  (vector-signed-scale
                   'factor
                   (vector-add
                    empty (cons-vector 'right-head 'right-tail)))
                  (vector-add
                   (vector-signed-scale 'factor empty)
                   (vector-signed-scale
                    'factor
                    (cons-vector 'right-head 'right-tail))))
                 'current-shape)))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-additive (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-shape
                     (vector-same-shape current-left 'current-right)]]
                   (vector-equivalent
                    (vector-signed-scale
                     'factor (vector-add current-left 'current-right))
                    (vector-add
                     (vector-signed-scale 'factor current-left)
                     (vector-signed-scale
                      'factor 'current-right)))))]
             (function/lam
              [['current-right vector-type]]
              (vector-rec
               right-motive
               (function/lam
                [['current-shape
                  (vector-same-shape current-left (nil-vector))]]
                (absurd
                 (vector-equivalent
                  (vector-signed-scale
                   'factor (vector-add current-left (nil-vector)))
                  (vector-add
                   (vector-signed-scale 'factor current-left)
                   (vector-signed-scale 'factor (nil-vector))))
                 'current-shape))
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-shape
                   (vector-same-shape
                    current-left
                    (cons-vector 'right-head 'right-tail))]]
                 (let [head-shape
                       (signed-equivalent
                        signed-zero signed-zero)
                       tail-shape
                       (vector-same-shape 'left-tail 'right-tail)]
                   (conjoin
                    (signed-equivalent
                     (scale-difference
                      'factor (signed-add 'left-head 'right-head))
                     (signed-add
                      (scale-difference 'factor 'left-head)
                      (scale-difference 'factor 'right-head)))
                    (vector-equivalent
                     (vector-signed-scale
                      'factor (vector-add 'left-tail 'right-tail))
                     (vector-add
                      (vector-signed-scale 'factor 'left-tail)
                      (vector-signed-scale 'factor 'right-tail)))
                    (app
                     (function/const* 'signed/scale-difference-additive [])
                     'factor 'left-head 'right-head)
                    (app 'tail-additive 'right-tail
                         (proposition-right
                          head-shape tail-shape 'current-shape))))))
               'current-right))))]
      (app (vector-rec outer-motive outer-base outer-step 'left)
           'right 'shape)))})

(def vector-signed-scale-compose-spec
  {:name 'vector/signed-scale-compose :universes []
   :type
   (function/forall
    [['outer signed] ['inner signed] ['values vector-type]]
    (vector-equivalent
     (vector-signed-scale
      'outer (vector-signed-scale 'inner 'values))
     (vector-signed-scale
      (signed-multiply 'outer 'inner) 'values)))
   :value
   (function/lam
    [['outer signed] ['inner signed] ['values vector-type]]
    (let [factor-product (signed-multiply 'outer 'inner)
          motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-signed-scale
             'outer (vector-signed-scale 'inner 'current))
            (vector-signed-scale factor-product 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-composes (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (scale-difference
              'outer (scale-difference 'inner 'head))
             (scale-difference factor-product 'head))
            (vector-equivalent
             (vector-signed-scale
              'outer (vector-signed-scale 'inner 'tail))
             (vector-signed-scale factor-product 'tail))
            (app (function/const* 'signed/scale-difference-compose [])
                 'outer 'inner 'head)
            'tail-composes))]
      (vector-rec motive trivial step 'values)))})

(def matrix-signed-scale-additive-spec
  {:name 'matrix/signed-scale-additive :universes []
   :type
   (function/forall
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (matrix-equivalent
     (matrix-signed-scale
      'factor (matrix-addition 'left 'right))
     (matrix-addition
      (matrix-signed-scale 'factor 'left)
      (matrix-signed-scale 'factor 'right))))
   :value
   (function/lam
    [['factor signed] ['left matrix-type] ['right matrix-type]
     ['shape (matrix-same-shape 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-right matrix-type]
             ['current-shape
              (matrix-same-shape 'current-left 'current-right)]]
            (matrix-equivalent
             (matrix-signed-scale
              'factor (matrix-addition 'current-left 'current-right))
             (matrix-addition
              (matrix-signed-scale 'factor 'current-left)
              (matrix-signed-scale 'factor 'current-right)))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-right matrix-type]]
                 (function/forall
                  [['current-shape
                    (matrix-same-shape empty 'current-right)]]
                  (matrix-equivalent
                   (matrix-signed-scale
                    'factor (matrix-addition empty 'current-right))
                   (matrix-addition
                    (matrix-signed-scale 'factor empty)
                    (matrix-signed-scale
                     'factor 'current-right)))))]
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
                  (matrix-signed-scale
                   'factor
                   (matrix-addition
                    empty (cons-matrix 'right-row 'right-tail)))
                  (matrix-addition
                   (matrix-signed-scale 'factor empty)
                   (matrix-signed-scale
                    'factor
                    (cons-matrix 'right-row 'right-tail))))
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
                   (matrix-equivalent
                    (matrix-signed-scale
                     'factor
                     (matrix-addition current-left 'current-right))
                    (matrix-addition
                     (matrix-signed-scale 'factor current-left)
                     (matrix-signed-scale
                      'factor 'current-right)))))]
             (function/lam
              [['current-right matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-shape
                  (matrix-same-shape current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (matrix-signed-scale
                   'factor
                   (matrix-addition current-left (nil-matrix)))
                  (matrix-addition
                   (matrix-signed-scale 'factor current-left)
                   (matrix-signed-scale 'factor (nil-matrix))))
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
                     (vector-signed-scale
                      'factor (vector-add 'left-row 'right-row))
                     (vector-add
                      (vector-signed-scale 'factor 'left-row)
                      (vector-signed-scale 'factor 'right-row)))
                    (matrix-equivalent
                     (matrix-signed-scale
                      'factor
                      (matrix-addition 'left-tail 'right-tail))
                     (matrix-addition
                      (matrix-signed-scale 'factor 'left-tail)
                      (matrix-signed-scale 'factor 'right-tail)))
                    (app
                     (function/const* 'vector/signed-scale-additive [])
                     'factor 'left-row 'right-row
                     (proposition-left
                      head-shape tail-shape 'current-shape))
                    (app 'tail-additive 'right-tail
                         (proposition-right
                          head-shape tail-shape 'current-shape))))))
               'current-right))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'right 'shape)))})

(def matrix-signed-scale-compose-spec
  {:name 'matrix/signed-scale-compose :universes []
   :type
   (function/forall
    [['outer signed] ['inner signed] ['rows matrix-type]]
    (matrix-equivalent
     (matrix-signed-scale
      'outer (matrix-signed-scale 'inner 'rows))
     (matrix-signed-scale
      (signed-multiply 'outer 'inner) 'rows)))
   :value
   (function/lam
    [['outer signed] ['inner signed] ['rows matrix-type]]
    (let [factor-product (signed-multiply 'outer 'inner)
          motive
          (function/lam
           [['current matrix-type]]
           (matrix-equivalent
            (matrix-signed-scale
             'outer (matrix-signed-scale 'inner 'current))
            (matrix-signed-scale factor-product 'current)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-composes (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-signed-scale
              'outer (vector-signed-scale 'inner 'row))
             (vector-signed-scale factor-product 'row))
            (matrix-equivalent
             (matrix-signed-scale
              'outer (matrix-signed-scale 'inner 'tail))
             (matrix-signed-scale factor-product 'tail))
            (app (function/const* 'vector/signed-scale-compose [])
                 'outer 'inner 'row)
            'tail-composes))]
      (matrix-rec motive trivial step 'rows)))})

(def definition-specs [])
(def theorem-specs
  [scale-difference-additive-spec
   scale-difference-compose-spec
   vector-signed-scale-additive-spec
   vector-signed-scale-compose-spec
   matrix-signed-scale-additive-spec
   matrix-signed-scale-compose-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.subtract-linear])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/multiply-associative :signed-multiply-associative associative/multiply-associative-spec) (support/extend-with :finite-matrix-signed-scale-algebra theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.signed-scale-algebra))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
