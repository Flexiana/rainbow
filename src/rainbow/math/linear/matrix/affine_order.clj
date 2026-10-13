(ns rainbow.math.linear.matrix.affine-order
  "Order and interval laws for signed affine finite-matrix action.

  `matrix/affine-action rows offset values` is the Bellman-shaped map
  `offset + rows·values`.  Translation preserves pointwise order, so the
  matrix-action monotone, antitone, joint, and interval laws lift to this
  affine map without hidden shape assumptions.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.interval-order :as interval]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.add-order :as add-order]))

(def z [:zero])
(def t [:succ z])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- both [a b]
  (app (function/const* 'proposition/conjunction []) a b))
(defn- conjp [a b pa pb]
  (app (function/const* 'proposition/conjoin []) a b pa pb))

(def affine-action-spec
  {:name 'matrix/affine-action :kind :definition :universes []
   :type (function/arrow matrix-type vector-type vector-type vector-type)
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['values vector-type]]
    (vadd 'offset (action 'rows 'values)))})

(def affine-action-unfold-spec
  {:name 'matrix/affine-action-unfold :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['values vector-type]]
    (veq (affine 'rows 'offset 'values)
         (vadd 'offset (action 'rows 'values))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['values vector-type]]
    (app (function/const* 'vector/equivalent-reflexive [])
         (vadd 'offset (action 'rows 'values))))})

(def affine-action-monotone-values-spec
  {:name 'matrix/affine-action-monotone-values :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['ordered (vle 'left 'right)]]
    (vle (affine 'rows 'offset 'left)
         (affine 'rows 'offset 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['ordered (vle 'left 'right)]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'rows 'left) (action 'rows 'right) 'offset
         (app (function/const* 'matrix/vector-multiply-monotone-values [])
              'rows 'left 'right 'rows-positive 'ordered)))})

(def affine-action-antitone-values-spec
  {:name 'matrix/affine-action-antitone-values :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['ordered (vle 'left 'right)]]
    (vle (affine 'rows 'offset 'right)
         (affine 'rows 'offset 'left)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-negative (mle 'rows (mz 'rows))]
     ['ordered (vle 'left 'right)]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'rows 'right) (action 'rows 'left) 'offset
         (app (function/const* 'matrix/vector-multiply-antitone-values [])
              'rows 'left 'right 'rows-negative 'ordered)))})

(def affine-action-monotone-rows-spec
  {:name 'matrix/affine-action-monotone-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-positive (vle (vz 'values) 'values)]]
    (vle (affine 'left 'offset 'values)
         (affine 'right 'offset 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-positive (vle (vz 'values) 'values)]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'left 'values) (action 'right 'values) 'offset
         (app (function/const* 'matrix/vector-multiply-monotone-rows [])
              'left 'right 'values 'ordered 'values-positive)))})

(def affine-action-antitone-rows-spec
  {:name 'matrix/affine-action-antitone-rows :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-negative (vle 'values (vz 'values))]]
    (vle (affine 'right 'offset 'values)
         (affine 'left 'offset 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['ordered (mle 'left 'right)]
     ['values-negative (vle 'values (vz 'values))]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'right 'values) (action 'left 'values) 'offset
         (app (function/const* 'matrix/vector-multiply-antitone-rows [])
              'left 'right 'values 'ordered 'values-negative)))})

(def affine-action-monotone-offset-spec
  {:name 'matrix/affine-action-monotone-offset :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['values vector-type] ['ordered (vle 'left 'right)]]
    (vle (affine 'rows 'left 'values)
         (affine 'rows 'right 'values)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['values vector-type] ['ordered (vle 'left 'right)]]
    (app (function/const* 'vector/add-right-monotone [])
         'left 'right (action 'rows 'values) 'ordered))})

(def affine-action-monotone-offset-values-spec
  {:name 'matrix/affine-action-monotone-offset-values :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (vle (affine 'rows 'source-offset 'source-values)
         (affine 'rows 'destination-offset 'destination-values)))
   :value
   (function/lam
    [['rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (app (function/const* 'vector/add-monotone [])
         'source-offset 'destination-offset
         (action 'rows 'source-values)
         (action 'rows 'destination-values)
         'offset-ordered
         (app (function/const* 'matrix/vector-multiply-monotone-values [])
              'rows 'source-values 'destination-values
              'rows-positive 'values-ordered)))})

(def affine-action-monotone-offset-rows-spec
  {:name 'matrix/affine-action-monotone-offset-rows :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['values vector-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]]
    (vle (affine 'source-rows 'source-offset 'values)
         (affine 'destination-rows 'destination-offset 'values)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['values vector-type]
     ['values-positive (vle (vz 'values) 'values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]]
    (app (function/const* 'vector/add-monotone [])
         'source-offset 'destination-offset
         (action 'source-rows 'values)
         (action 'destination-rows 'values)
         'offset-ordered
         (app (function/const* 'matrix/vector-multiply-monotone-rows [])
              'source-rows 'destination-rows 'values
              'rows-ordered 'values-positive)))})

(def affine-action-monotone-spec
  {:name 'matrix/affine-action-monotone :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-values-positive
      (vle (vz 'source-values) 'source-values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (vle (affine 'source-rows 'offset 'source-values)
         (affine 'destination-rows 'offset 'destination-values)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-values-positive
      (vle (vz 'source-values) 'source-values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'source-rows 'source-values)
         (action 'destination-rows 'destination-values)
         'offset
         (app (function/const* 'matrix/vector-multiply-monotone [])
              'source-rows 'destination-rows
              'source-values 'destination-values
              'destination-rows-positive 'source-values-positive
              'rows-ordered 'values-ordered)))})

(def affine-action-antitone-spec
  {:name 'matrix/affine-action-antitone :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-negative
      (mle 'destination-rows (mz 'destination-rows))]
     ['source-values-negative
      (vle 'source-values (vz 'source-values))]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (vle (affine 'destination-rows 'offset 'destination-values)
         (affine 'source-rows 'offset 'source-values)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-negative
      (mle 'destination-rows (mz 'destination-rows))]
     ['source-values-negative
      (vle 'source-values (vz 'source-values))]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (app (function/const* 'vector/add-left-monotone [])
         (action 'destination-rows 'destination-values)
         (action 'source-rows 'source-values)
         'offset
         (app (function/const* 'matrix/vector-multiply-antitone [])
              'source-rows 'destination-rows
              'source-values 'destination-values
              'destination-rows-negative 'source-values-negative
              'rows-ordered 'values-ordered)))})

(def affine-action-monotone-all-spec
  {:name 'matrix/affine-action-monotone-all :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-values-positive
      (vle (vz 'source-values) 'source-values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (vle (affine 'source-rows 'source-offset 'source-values)
         (affine 'destination-rows
                 'destination-offset 'destination-values)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-values vector-type] ['destination-values vector-type]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-values-positive
      (vle (vz 'source-values) 'source-values)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['values-ordered (vle 'source-values 'destination-values)]]
    (app (function/const* 'vector/add-monotone [])
         'source-offset 'destination-offset
         (action 'source-rows 'source-values)
         (action 'destination-rows 'destination-values)
         'offset-ordered
         (app (function/const* 'matrix/vector-multiply-monotone [])
              'source-rows 'destination-rows
              'source-values 'destination-values
              'destination-rows-positive 'source-values-positive
              'rows-ordered 'values-ordered)))})

(def affine-action-bounds-offset-spec
  {:name 'matrix/affine-action-bounds-offset :universes []
   :type
   (function/forall
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['values vector-type]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (both (vle (affine 'rows 'lower 'values)
               (affine 'rows 'value 'values))
          (vle (affine 'rows 'value 'values)
               (affine 'rows 'upper 'values))))
   :value
   (function/lam
    [['rows matrix-type]
     ['lower vector-type] ['value vector-type] ['upper vector-type]
     ['values vector-type]
     ['lower-ordered (vle 'lower 'value)]
     ['upper-ordered (vle 'value 'upper)]]
    (conjp
     (vle (affine 'rows 'lower 'values)
          (affine 'rows 'value 'values))
     (vle (affine 'rows 'value 'values)
          (affine 'rows 'upper 'values))
     (app (function/const* 'matrix/affine-action-monotone-offset [])
          'rows 'lower 'value 'values 'lower-ordered)
     (app (function/const* 'matrix/affine-action-monotone-offset [])
          'rows 'value 'upper 'values 'upper-ordered)))})

(defn- affine-value-bounds-spec [nonnegative?]
  (let [name (if nonnegative?
               'matrix/affine-action-bounds-nonnegative-rows
               'matrix/affine-action-bounds-nonpositive-rows)
        sign-name (if nonnegative? 'rows-positive 'rows-negative)
        sign-type (if nonnegative?
                    (mle (mz 'rows) 'rows)
                    (mle 'rows (mz 'rows)))
        low (if nonnegative? 'lower 'upper)
        high (if nonnegative? 'upper 'lower)
        law (if nonnegative?
              'matrix/affine-action-monotone-values
              'matrix/affine-action-antitone-values)]
    {:name name :universes []
     :type
     (function/forall
      [['rows matrix-type] ['offset vector-type]
       ['lower vector-type] ['value vector-type] ['upper vector-type]
       [sign-name sign-type]
       ['lower-ordered (vle 'lower 'value)]
       ['upper-ordered (vle 'value 'upper)]]
      (both (vle (affine 'rows 'offset low)
                 (affine 'rows 'offset 'value))
            (vle (affine 'rows 'offset 'value)
                 (affine 'rows 'offset high))))
     :value
     (function/lam
      [['rows matrix-type] ['offset vector-type]
       ['lower vector-type] ['value vector-type] ['upper vector-type]
       [sign-name sign-type]
       ['lower-ordered (vle 'lower 'value)]
       ['upper-ordered (vle 'value 'upper)]]
      (conjp
       (vle (affine 'rows 'offset low)
            (affine 'rows 'offset 'value))
       (vle (affine 'rows 'offset 'value)
            (affine 'rows 'offset high))
       (if nonnegative?
         (app (function/const* law []) 'rows 'offset 'lower 'value
              sign-name 'lower-ordered)
         (app (function/const* law []) 'rows 'offset 'value 'upper
              sign-name 'upper-ordered))
       (if nonnegative?
         (app (function/const* law []) 'rows 'offset 'value 'upper
              sign-name 'upper-ordered)
         (app (function/const* law []) 'rows 'offset 'lower 'value
              sign-name 'lower-ordered))))}))

(def affine-action-bounds-nonnegative-rows-spec
  (affine-value-bounds-spec true))
(def affine-action-bounds-nonpositive-rows-spec
  (affine-value-bounds-spec false))

(defn- affine-row-bounds-spec [nonnegative?]
  (let [name (if nonnegative?
               'matrix/affine-action-bounds-nonnegative-values
               'matrix/affine-action-bounds-nonpositive-values)
        sign-name (if nonnegative? 'values-positive 'values-negative)
        sign-type (if nonnegative?
                    (vle (vz 'values) 'values)
                    (vle 'values (vz 'values)))
        low (if nonnegative? 'lower 'upper)
        high (if nonnegative? 'upper 'lower)
        law (if nonnegative?
              'matrix/affine-action-monotone-rows
              'matrix/affine-action-antitone-rows)]
    {:name name :universes []
     :type
     (function/forall
      [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
       ['offset vector-type] ['values vector-type]
       [sign-name sign-type]
       ['lower-ordered (mle 'lower 'value)]
       ['upper-ordered (mle 'value 'upper)]]
      (both (vle (affine low 'offset 'values)
                 (affine 'value 'offset 'values))
            (vle (affine 'value 'offset 'values)
                 (affine high 'offset 'values))))
     :value
     (function/lam
      [['lower matrix-type] ['value matrix-type] ['upper matrix-type]
       ['offset vector-type] ['values vector-type]
       [sign-name sign-type]
       ['lower-ordered (mle 'lower 'value)]
       ['upper-ordered (mle 'value 'upper)]]
      (conjp
       (vle (affine low 'offset 'values)
            (affine 'value 'offset 'values))
       (vle (affine 'value 'offset 'values)
            (affine high 'offset 'values))
       (if nonnegative?
         (app (function/const* law []) 'lower 'value 'offset 'values
              'lower-ordered sign-name)
         (app (function/const* law []) 'value 'upper 'offset 'values
              'upper-ordered sign-name))
       (if nonnegative?
         (app (function/const* law []) 'value 'upper 'offset 'values
              'upper-ordered sign-name)
         (app (function/const* law []) 'lower 'value 'offset 'values
              'lower-ordered sign-name))))}))

(def affine-action-bounds-nonnegative-values-spec
  (affine-row-bounds-spec true))
(def affine-action-bounds-nonpositive-values-spec
  (affine-row-bounds-spec false))

(def definition-specs [affine-action-spec])
(def theorem-specs
  [affine-action-unfold-spec
   affine-action-monotone-values-spec
   affine-action-antitone-values-spec
   affine-action-monotone-rows-spec
   affine-action-antitone-rows-spec
   affine-action-monotone-offset-spec
   affine-action-monotone-offset-values-spec
   affine-action-monotone-offset-rows-spec
   affine-action-monotone-spec
   affine-action-antitone-spec
   affine-action-monotone-all-spec
   affine-action-bounds-offset-spec
   affine-action-bounds-nonnegative-rows-spec
   affine-action-bounds-nonpositive-rows-spec
   affine-action-bounds-nonnegative-values-spec
   affine-action-bounds-nonpositive-values-spec])

(defn- extend-add-order-if-missing [env]
  (reduce
   (fn [current spec]
     (if (environment/resolve-id current (:name spec))
       current
       (support/extend-with current :vector-add-order [spec])))
   env
   [add-order/add-right-monotone-spec
    add-order/add-left-monotone-spec
    add-order/add-monotone-spec]))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.interval-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env extend-add-order-if-missing (support/extend-with :finite-matrix-affine-order (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
