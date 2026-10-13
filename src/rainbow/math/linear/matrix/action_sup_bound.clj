(ns rainbow.math.linear.matrix.action-sup-bound
  "Lift rowwise dot-distance bounds to a matrix-action sup bound.

  Matrix-vector multiplication maps dot product over the row list.  If every
  member row moves two inputs by at most a common signed upper bound, and zero
  is below that bound, structural induction shows the whole output vector is
  within the same sup-distance bound.  This separates the generic operator
  lift from later row-norm or stochastic-row certificates.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.matrix :as matrix]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.vector-sup-distance :as sup]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- nil-matrix []
  (app (function/const* 'data/nil [type-level]) vector-type))
(defn- cons-matrix [row tail]
  (app (function/const* 'data/cons [type-level])
       vector-type row tail))
(defn- list-rec [motive base step rows]
  (app (function/const* 'data/List.rec [type-level zero-level])
       vector-type motive base step rows))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- dot [row values]
  (app (function/const* 'vector/dot []) row values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rowwise-bound [rows left right upper]
  (function/forall
   [['row vector-type]
    ['member (membership rows 'row)]]
   (sle (scalar-distance (dot 'row left)
                         (dot 'row right))
        upper)))

(def vector-multiply-sup-distance-bounded-spec
  {:name 'matrix/vector-multiply-sup-distance-bounded :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['upper signed] ['zero-upper (sle signed-zero 'upper)]
     ['rowwise (rowwise-bound 'rows 'left 'right 'upper)]]
    (sle (sup-distance (action 'rows 'left)
                       (action 'rows 'right))
         'upper))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['upper signed] ['zero-upper (sle signed-zero 'upper)]
     ['rowwise (rowwise-bound 'rows 'left 'right 'upper)]]
    (let [motive
          (function/lam
           [['current-rows matrix-type]]
           (function/arrow
            (rowwise-bound 'current-rows 'left 'right 'upper)
            (sle (sup-distance (action 'current-rows 'left)
                               (action 'current-rows 'right))
                 'upper)))
          base
          (function/lam
           [['ignored (rowwise-bound
                       (nil-matrix) 'left 'right 'upper)]]
           'zero-upper)
          step
          (function/lam
           [['head-row vector-type] ['tail-rows matrix-type]
            ['tail-bounded
             (function/arrow
              (rowwise-bound 'tail-rows 'left 'right 'upper)
              (sle (sup-distance (action 'tail-rows 'left)
                                 (action 'tail-rows 'right))
                   'upper))]
            ['current-rowwise
             (rowwise-bound
              (cons-matrix 'head-row 'tail-rows)
              'left 'right 'upper)]]
           (let [head-equality
                 (function/equality
                  type-level vector-type 'head-row 'head-row)
                 head-member
                 (app
                  (function/const* 'proposition/left-disjunct [])
                  head-equality
                  (membership 'tail-rows 'head-row)
                  (app
                   (function/const* 'equality/reflexive [type-level])
                   vector-type 'head-row))
                 tail-rowwise
                 (function/lam
                  [['row vector-type]
                   ['tail-member (membership 'tail-rows 'row)]]
                  (app
                   'current-rowwise 'row
                   (app
                    (function/const* 'proposition/right-disjunct [])
                    (function/equality
                     type-level vector-type 'row 'head-row)
                    (membership 'tail-rows 'row)
                    'tail-member)))]
             (app
              (function/const*
               'vector/sup-distance-cons-bounded [])
              (dot 'head-row 'left) (action 'tail-rows 'left)
              (dot 'head-row 'right) (action 'tail-rows 'right)
              'upper
              (app 'current-rowwise 'head-row head-member)
              (app 'tail-bounded tail-rowwise))))]
      (app (list-rec motive base step 'rows) 'rowwise)))})

(def definition-specs [])
(def theorem-specs [vector-multiply-sup-distance-bounded-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.matrix rainbow.math.rational.signed.vector-sup-distance])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-action-sup-bound theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.action-sup-bound))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
