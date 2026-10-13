(ns rainbow.math.linear.matrix.affine-half-iterate-contraction
  "Shape preservation and one-step contraction for half-row affine iteration.

  Matrix action output length depends only on the row count.  Consequently two
  affine images have the same shape whenever the offset fits one reference
  action, and equal-shaped initial states remain equal-shaped through every
  finite iterate.  The concrete half-row Lipschitz theorem can therefore be
  applied at every horizon, proving that successive paired iterates halve their
  signed sup distance.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-iterate :as iterate]
            [rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness
             :as half]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-add :as shape-add]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-half
  (function/app
   (function/const* 'signed/from-nnrat [])
   (function/const* 'nnrat/half [])))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def matrix-type
  (function/app (function/const* 'data/List [type-level]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value] (app successor value))
(defn- prop-nat-rec [motive base step value]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- sup-distance [left right]
  (app (function/const* 'vector/sup-distance []) left right))
(defn- vector-sum [values]
  (app (function/const* 'vector/sum []) values))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine-action [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- affine-iterate [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- membership [rows row]
  (app (function/const* 'list/membership [zero-level])
       vector-type rows row))
(defn- rows-positive [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (vector-at-most (zero-like 'row) 'row)))
(defn- half-row-sums [rows]
  (function/forall
   [['row vector-type] ['member (membership rows 'row)]]
   (sle (vector-sum 'row) signed-half)))
(defn- same-shape-symmetric [left right same]
  (app (function/const* 'vector/same-shape-symmetric [])
       left right same))
(defn- same-shape-transitive [left middle right first second]
  (app (function/const* 'vector/same-shape-transitive [])
       left middle right first second))
(defn- reference-offset-shape [rows offset reference current offset-reference]
  (same-shape-transitive
   offset (action rows reference) (action rows current)
   offset-reference
   (app (function/const* 'matrix/vector-multiply-output-shape [])
        rows reference current)))

(def affine-action-output-shape-spec
  {:name 'matrix/affine-action-output-shape :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]]
    (same-shape (affine-action 'rows 'offset 'left)
                (affine-action 'rows 'offset 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]]
    (let [left-action (action 'rows 'left)
          right-action (action 'rows 'right)
          left-output (affine-action 'rows 'offset 'left)
          right-output (affine-action 'rows 'offset 'right)
          action-shape
          (app (function/const* 'matrix/vector-multiply-output-shape [])
               'rows 'left 'right)
          right-offset-shape
          (same-shape-transitive
           'offset left-action right-action 'offset-shape action-shape)
          left-output-offset
          (app (function/const* 'vector/add-preserves-left-shape [])
               'offset left-action 'offset-shape)
          right-output-offset
          (app (function/const* 'vector/add-preserves-left-shape [])
               'offset right-action right-offset-shape)]
      (same-shape-transitive
       left-output 'offset right-output
       left-output-offset
       (same-shape-symmetric
        right-output 'offset right-output-offset))))})

(def affine-iterate-output-shape-spec
  {:name 'matrix/affine-iterate-output-shape :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['steps nat]]
    (same-shape (affine-iterate 'rows 'offset 'steps 'left)
                (affine-iterate 'rows 'offset 'steps 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['steps nat]]
    (let [left-at
          (fn [n] (affine-iterate 'rows 'offset n 'left))
          right-at
          (fn [n] (affine-iterate 'rows 'offset n 'right))
          motive
          (function/lam
           [['n nat]] (same-shape (left-at 'n) (right-at 'n)))
          step
          (function/lam
           [['n nat] ['ignored (app motive 'n)]]
           (app
            (function/const* 'matrix/affine-action-output-shape [])
            'rows 'offset (left-at 'n) (right-at 'n)
            (reference-offset-shape
             'rows 'offset 'left (left-at 'n) 'offset-shape)))]
      (prop-nat-rec motive 'initial-shape step 'steps)))})

(def affine-half-iterate-sup-distance-step-spec
  {:name 'matrix/affine-half-iterate-sup-distance-step :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (half-row-sums 'rows)]
     ['steps nat]]
    (sle
     (sup-distance
      (affine-iterate 'rows 'offset (succ 'steps) 'left)
      (affine-iterate 'rows 'offset (succ 'steps) 'right))
     (smul
      signed-half
      (sup-distance
       (affine-iterate 'rows 'offset 'steps 'left)
       (affine-iterate 'rows 'offset 'steps 'right)))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['initial-shape (same-shape 'left 'right)]
     ['offset-shape (same-shape 'offset (action 'rows 'left))]
     ['positive-rows (rows-positive 'rows)]
     ['bounded-sums (half-row-sums 'rows)]
     ['steps nat]]
    (let [left-current
          (affine-iterate 'rows 'offset 'steps 'left)
          right-current
          (affine-iterate 'rows 'offset 'steps 'right)
          current-shape
          (app (function/const* 'matrix/affine-iterate-output-shape [])
               'rows 'offset 'left 'right
               'initial-shape 'offset-shape 'steps)
          current-offset-shape
          (reference-offset-shape
           'rows 'offset 'left left-current 'offset-shape)]
      (app
       (function/const* 'matrix/affine-action-row-sum-lipschitz [])
       'rows 'offset left-current right-current signed-half
       (function/const* 'signed/zero-at-most-half [])
       current-shape current-offset-shape
       'positive-rows 'bounded-sums)))})

(def definition-specs [])
(def theorem-specs
  [affine-action-output-shape-spec
   affine-iterate-output-shape-spec
   affine-half-iterate-sup-distance-step-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- extend-specs-if-missing [env milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   env specs))

(defn extend-environment [env]
  (-> env
      half/extend-environment
      (extend-spec-if-missing
       'matrix/affine-iterate :finite-matrix-affine-iterate
       iterate/affine-iterate-spec)
      (extend-specs-if-missing :vector-shape-add shape-add/theorem-specs)
      (support/extend-with
       :finite-matrix-affine-half-iterate-contraction theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
