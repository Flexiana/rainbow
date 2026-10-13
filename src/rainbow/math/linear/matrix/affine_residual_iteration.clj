(ns rainbow.math.linear.matrix.affine-residual-iteration
  "Finite value-iteration guarantees from linear residual inequalities.

  With nonnegative rows, `x - rows*x <= offset` certifies an ascending affine
  trajectory and `offset <= x - rows*x` certifies a descending one.  A lower
  certificate and an upper certificate therefore form an invariant interval
  for every finite iterate started between them.  Only the value/image shape
  needed to add the matrix image back is assumed.  Theorem-only,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual-order
             :as residual-order]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app successor n))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))

(def affine-iterate-residual-upper-ascending-spec
  {:name 'matrix/affine-iterate-residual-upper-ascending :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['value-image-shape
      (same-shape 'initial (action 'rows 'initial))]
     ['residual-upper
      (vle (vsub 'initial (action 'rows 'initial)) 'offset)]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset 'steps 'initial)
         (iterate-affine 'rows 'offset (succ 'steps) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['value-image-shape
      (same-shape 'initial (action 'rows 'initial))]
     ['residual-upper
      (vle (vsub 'initial (action 'rows 'initial)) 'offset)]
     ['steps nat]]
    (let [subsolution
          (app
           (function/const*
            'matrix/affine-residual-upper-bound-implies-subsolution [])
           'rows 'offset 'initial 'value-image-shape 'residual-upper)]
      (app
       (function/const* 'matrix/affine-iterate-subsolution-ascending [])
       'rows 'offset 'initial 'rows-positive subsolution 'steps)))})

(def affine-iterate-residual-lower-descending-spec
  {:name 'matrix/affine-iterate-residual-lower-descending :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['value-image-shape
      (same-shape 'initial (action 'rows 'initial))]
     ['residual-lower
      (vle 'offset (vsub 'initial (action 'rows 'initial)))]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset (succ 'steps) 'initial)
         (iterate-affine 'rows 'offset 'steps 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['value-image-shape
      (same-shape 'initial (action 'rows 'initial))]
     ['residual-lower
      (vle 'offset (vsub 'initial (action 'rows 'initial)))]
     ['steps nat]]
    (let [supersolution
          (app
           (function/const*
            'matrix/affine-residual-lower-bound-implies-supersolution [])
           'rows 'offset 'initial 'value-image-shape 'residual-lower)]
      (app
       (function/const* 'matrix/affine-iterate-supersolution-descending [])
       'rows 'offset 'initial 'rows-positive supersolution 'steps)))})

(def affine-iterate-residual-invariant-interval-spec
  {:name 'matrix/affine-iterate-residual-invariant-interval :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['initial vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-initial (vle 'lower 'initial)]
     ['initial-upper (vle 'initial 'upper)]
     ['steps nat]]
    (let [result (iterate-affine 'rows 'offset 'steps 'initial)]
      (both (vle 'lower result) (vle result 'upper))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['initial vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-image-shape
      (same-shape 'lower (action 'rows 'lower))]
     ['upper-image-shape
      (same-shape 'upper (action 'rows 'upper))]
     ['lower-residual-upper
      (vle (vsub 'lower (action 'rows 'lower)) 'offset)]
     ['upper-residual-lower
      (vle 'offset (vsub 'upper (action 'rows 'upper)))]
     ['lower-initial (vle 'lower 'initial)]
     ['initial-upper (vle 'initial 'upper)]
     ['steps nat]]
    (let [lower-subsolution
          (app
           (function/const*
            'matrix/affine-residual-upper-bound-implies-subsolution [])
           'rows 'offset 'lower 'lower-image-shape
           'lower-residual-upper)
          upper-supersolution
          (app
           (function/const*
            'matrix/affine-residual-lower-bound-implies-supersolution [])
           'rows 'offset 'upper 'upper-image-shape
           'upper-residual-lower)]
      (app
       (function/const* 'matrix/affine-iterate-invariant-interval [])
       'rows 'offset 'lower 'initial 'upper
       'rows-positive lower-subsolution upper-supersolution
       'lower-initial 'initial-upper 'steps)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-residual-upper-ascending-spec
   affine-iterate-residual-lower-descending-spec
   affine-iterate-residual-invariant-interval-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-residual-iteration theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-residual-iteration))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
