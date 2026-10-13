(ns rainbow.math.linear.matrix.affine-invariant-interval
  "Invariant intervals for finite signed affine value iteration.

  Under a nonnegative matrix, a Bellman subsolution lies below every iterate
  started from itself and a supersolution lies above every iterate started from
  itself.  Monotonicity then proves that any initial value between those two
  certificates remains trapped between them at every finite step.  Theorem-only,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-horizon-order
             :as horizon-order]
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
(defn- prop-nat-rec [m b s n]
  (app (function/const* 'data/Nat.rec [z]) m b s n))
(defn- vz [x] (app (function/const* 'vector/zero-like []) x))
(defn- vle [a b] (app (function/const* 'vector/at-most []) a b))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- mz [x] (app (function/const* 'matrix/zero-like []) x))
(defn- mle [a b] (app (function/const* 'matrix/at-most []) a b))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- both [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- at-most-reflexive [values]
  (app (function/const* 'vector/equivalent-to-at-most [])
       values values
       (app (function/const* 'vector/equivalent-reflexive []) values)))
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-above-subsolution-spec
  {:name 'matrix/affine-iterate-above-subsolution :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['subsolution vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['post-fixed
      (vle 'subsolution (affine 'rows 'offset 'subsolution))]
     ['steps nat]]
    (vle 'subsolution
         (iterate-affine 'rows 'offset 'steps 'subsolution)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['subsolution vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['post-fixed
      (vle 'subsolution (affine 'rows 'offset 'subsolution))]
     ['steps nat]]
    (let [at (fn [n]
               (iterate-affine 'rows 'offset n 'subsolution))
          motive (function/lam [['n nat]] (vle 'subsolution (at 'n)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (at-most-transitive
            'subsolution (at 'n) (at (succ 'n))
            'ih
            (app
             (function/const*
              'matrix/affine-iterate-subsolution-ascending [])
             'rows 'offset 'subsolution 'rows-positive 'post-fixed 'n)))]
      (prop-nat-rec motive (at-most-reflexive 'subsolution) step 'steps)))})

(def affine-iterate-below-supersolution-spec
  {:name 'matrix/affine-iterate-below-supersolution :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['supersolution vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['pre-fixed
      (vle (affine 'rows 'offset 'supersolution) 'supersolution)]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset 'steps 'supersolution)
         'supersolution))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['supersolution vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['pre-fixed
      (vle (affine 'rows 'offset 'supersolution) 'supersolution)]
     ['steps nat]]
    (let [at (fn [n]
               (iterate-affine 'rows 'offset n 'supersolution))
          motive (function/lam [['n nat]] (vle (at 'n) 'supersolution))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (at-most-transitive
            (at (succ 'n)) (at 'n) 'supersolution
            (app
             (function/const*
              'matrix/affine-iterate-supersolution-descending [])
             'rows 'offset 'supersolution 'rows-positive 'pre-fixed 'n)
            'ih))]
      (prop-nat-rec motive (at-most-reflexive 'supersolution) step 'steps)))})

(def affine-iterate-invariant-interval-spec
  {:name 'matrix/affine-iterate-invariant-interval :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['lower vector-type] ['initial vector-type] ['upper vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['lower-post-fixed (vle 'lower (affine 'rows 'offset 'lower))]
     ['upper-pre-fixed (vle (affine 'rows 'offset 'upper) 'upper)]
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
     ['lower-post-fixed (vle 'lower (affine 'rows 'offset 'lower))]
     ['upper-pre-fixed (vle (affine 'rows 'offset 'upper) 'upper)]
     ['lower-initial (vle 'lower 'initial)]
     ['initial-upper (vle 'initial 'upper)]
     ['steps nat]]
    (let [lower-at (iterate-affine 'rows 'offset 'steps 'lower)
          result (iterate-affine 'rows 'offset 'steps 'initial)
          upper-at (iterate-affine 'rows 'offset 'steps 'upper)
          lower-origin
          (app (function/const* 'matrix/affine-iterate-above-subsolution [])
               'rows 'offset 'lower 'rows-positive
               'lower-post-fixed 'steps)
          lower-trajectory
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'lower 'initial
               'rows-positive 'lower-initial 'steps)
          lower-bound
          (at-most-transitive
           'lower lower-at result lower-origin lower-trajectory)
          upper-trajectory
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'initial 'upper
               'rows-positive 'initial-upper 'steps)
          upper-origin
          (app (function/const* 'matrix/affine-iterate-below-supersolution [])
               'rows 'offset 'upper 'rows-positive
               'upper-pre-fixed 'steps)
          upper-bound
          (at-most-transitive
           result upper-at 'upper upper-trajectory upper-origin)]
      (conjoin (vle 'lower result) (vle result 'upper)
               lower-bound upper-bound)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-above-subsolution-spec
   affine-iterate-below-supersolution-spec
   affine-iterate-invariant-interval-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-horizon-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-invariant-interval theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-invariant-interval))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
