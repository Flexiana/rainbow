(ns rainbow.math.linear.matrix.multiply
  "Native matrix multiplication for row-major finite signed matrices.

  matrix/multiply left right maps each left row through matrix/vector-multiply
  against transpose right, so each result component is the exact dot product
  with a right column.  The operation is total under the established ragged
  semantics and agrees with ordinary matrix multiplication on compatible
  rectangular inputs.  Constructor and two-sided quotient congruence laws are
  native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.transpose-equivalence :as transpose-equivalence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

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
(defn- list-map [mapping rows]
  (app (function/const* 'list/map [type-level type-level])
       vector-type vector-type mapping rows))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- matrix-equivalent [left right]
  (app (function/const* 'matrix/equivalent []) left right))
(defn- vector-multiply [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- transpose [rows]
  (app (function/const* 'matrix/transpose []) rows))
(defn- multiply [left right]
  (app (function/const* 'matrix/multiply []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))
(defn- absurd [target impossible]
  (app impossible target))

(def multiply-spec
  {:name 'matrix/multiply :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow matrix-type matrix-type matrix-type)
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]]
    (list-map
     (function/lam
      [['row vector-type]]
      (vector-multiply (transpose 'right) 'row))
     'left))})

(def multiply-empty-left-spec
  {:name 'matrix/multiply-empty-left :universes []
   :type
   (function/forall
    [['right matrix-type]]
    (matrix-equivalent
     (multiply (nil-matrix) 'right)
     (nil-matrix)))
   :value
   (function/lam
    [['right matrix-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (nil-matrix)))})

(def multiply-cons-left-spec
  {:name 'matrix/multiply-cons-left :universes []
   :type
   (function/forall
    [['row vector-type] ['tail matrix-type] ['right matrix-type]]
    (matrix-equivalent
     (multiply (cons-matrix 'row 'tail) 'right)
     (cons-matrix
      (vector-multiply (transpose 'right) 'row)
      (multiply 'tail 'right))))
   :value
   (function/lam
    [['row vector-type] ['tail matrix-type] ['right matrix-type]]
    (app (function/const* 'matrix/equivalent-reflexive [])
         (cons-matrix
          (vector-multiply (transpose 'right) 'row)
          (multiply 'tail 'right))))})

(def multiply-respects-left-equivalence-spec
  {:name 'matrix/multiply-respects-left-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type]
     ['same (matrix-equivalent 'left 'equivalent-left)]]
    (matrix-equivalent
     (multiply 'left 'right)
     (multiply 'equivalent-left 'right)))
   :value
   (function/lam
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type]
     ['same (matrix-equivalent 'left 'equivalent-left)]]
    (let [outer-motive
          (function/lam
           [['current-left matrix-type]]
           (function/forall
            [['current-equivalent-left matrix-type]
             ['current-same
              (matrix-equivalent
               'current-left 'current-equivalent-left)]]
            (matrix-equivalent
             (multiply 'current-left 'right)
             (multiply 'current-equivalent-left 'right))))
          outer-base
          (let [empty (nil-matrix)
                right-motive
                (function/lam
                 [['current-equivalent-left matrix-type]]
                 (function/forall
                  [['current-same
                    (matrix-equivalent
                     empty 'current-equivalent-left)]]
                  (matrix-equivalent
                   (multiply empty 'right)
                   (multiply 'current-equivalent-left 'right))))]
            (function/lam
             [['current-equivalent-left matrix-type]]
             (matrix-rec
              right-motive
              (function/lam
               [['current-same (matrix-equivalent empty empty)]]
               trivial)
              (function/lam
               [['other-row vector-type] ['other-tail matrix-type]
                ['ignored (app right-motive 'other-tail)]]
               (function/lam
                [['current-same
                  (matrix-equivalent
                   empty (cons-matrix 'other-row 'other-tail))]]
                (absurd
                 (matrix-equivalent
                  (multiply empty 'right)
                  (multiply
                   (cons-matrix 'other-row 'other-tail) 'right))
                 'current-same)))
              'current-equivalent-left)))
          outer-step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-respects (app outer-motive 'tail)]]
           (let [current-left (cons-matrix 'row 'tail)
                 right-motive
                 (function/lam
                  [['current-equivalent-left matrix-type]]
                  (function/forall
                   [['current-same
                     (matrix-equivalent
                      current-left 'current-equivalent-left)]]
                   (matrix-equivalent
                    (multiply current-left 'right)
                    (multiply 'current-equivalent-left 'right))))]
             (function/lam
              [['current-equivalent-left matrix-type]]
              (matrix-rec
               right-motive
               (function/lam
                [['current-same
                  (matrix-equivalent current-left (nil-matrix))]]
                (absurd
                 (matrix-equivalent
                  (multiply current-left 'right)
                  (multiply (nil-matrix) 'right))
                 'current-same))
               (function/lam
                [['other-row vector-type] ['other-tail matrix-type]
                 ['ignored (app right-motive 'other-tail)]]
                (function/lam
                 [['current-same
                   (matrix-equivalent
                    current-left
                    (cons-matrix 'other-row 'other-tail))]]
                 (let [row-same
                       (proposition-left
                        (vector-equivalent 'row 'other-row)
                        (matrix-equivalent 'tail 'other-tail)
                        'current-same)
                       tail-same
                       (proposition-right
                        (vector-equivalent 'row 'other-row)
                        (matrix-equivalent 'tail 'other-tail)
                        'current-same)]
                   (conjoin
                    (vector-equivalent
                     (vector-multiply (transpose 'right) 'row)
                     (vector-multiply
                      (transpose 'right) 'other-row))
                    (matrix-equivalent
                     (multiply 'tail 'right)
                     (multiply 'other-tail 'right))
                    (app
                     (function/const*
                      'matrix/vector-multiply-respects-equivalence [])
                     (transpose 'right) 'row 'other-row row-same)
                    (app 'tail-respects 'other-tail tail-same)))))
               'current-equivalent-left))))]
      (app (matrix-rec outer-motive outer-base outer-step 'left)
           'equivalent-left 'same)))})

(def multiply-respects-right-equivalence-spec
  {:name 'matrix/multiply-respects-right-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['equivalent-right matrix-type]
     ['same (matrix-equivalent 'right 'equivalent-right)]]
    (matrix-equivalent
     (multiply 'left 'right)
     (multiply 'left 'equivalent-right)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['equivalent-right matrix-type]
     ['same (matrix-equivalent 'right 'equivalent-right)]]
    (let [transposes-same
          (app (function/const* 'matrix/transpose-respects-equivalence [])
               'right 'equivalent-right 'same)
          motive
          (function/lam
           [['current-left matrix-type]]
           (matrix-equivalent
            (multiply 'current-left 'right)
            (multiply 'current-left 'equivalent-right)))
          step
          (function/lam
           [['row vector-type] ['tail matrix-type]
            ['tail-respects (app motive 'tail)]]
           (conjoin
            (vector-equivalent
             (vector-multiply (transpose 'right) 'row)
             (vector-multiply (transpose 'equivalent-right) 'row))
            (matrix-equivalent
             (multiply 'tail 'right)
             (multiply 'tail 'equivalent-right))
            (app
             (function/const*
              'matrix/vector-multiply-respects-matrix-equivalence [])
             (transpose 'right) (transpose 'equivalent-right)
             'row transposes-same)
            'tail-respects))]
      (matrix-rec motive trivial step 'left)))})

(def multiply-respects-equivalence-spec
  {:name 'matrix/multiply-respects-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]]
    (matrix-equivalent
     (multiply 'left 'right)
     (multiply 'equivalent-left 'equivalent-right)))
   :value
   (function/lam
    [['left matrix-type] ['equivalent-left matrix-type]
     ['right matrix-type] ['equivalent-right matrix-type]
     ['left-same (matrix-equivalent 'left 'equivalent-left)]
     ['right-same (matrix-equivalent 'right 'equivalent-right)]]
    (app
     (function/const* 'matrix/equivalent-transitive [])
     (multiply 'left 'right)
     (multiply 'equivalent-left 'right)
     (multiply 'equivalent-left 'equivalent-right)
     (app
      (function/const* 'matrix/multiply-respects-left-equivalence [])
      'left 'equivalent-left 'right 'left-same)
     (app
      (function/const* 'matrix/multiply-respects-right-equivalence [])
      'equivalent-left 'right 'equivalent-right 'right-same)))})

(def definition-specs [multiply-spec])
(def theorem-specs
  [multiply-empty-left-spec
   multiply-cons-left-spec
   multiply-respects-left-equivalence-spec
   multiply-respects-right-equivalence-spec
   multiply-respects-equivalence-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.transpose-equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-matrix-multiply (into definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.matrix.multiply))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
