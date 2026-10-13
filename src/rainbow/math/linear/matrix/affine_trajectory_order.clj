(ns rainbow.math.linear.matrix.affine-trajectory-order
  "Successive-order laws for finite signed affine value iteration.

  Iterating once before an arbitrary finite run agrees with taking one more
  step.  For nonnegative matrices this shift law turns a Bellman subsolution
  `x <= F x` into an ascending trajectory and a supersolution `F x <= x` into
  a descending trajectory.  Theorem-only, kernel-checked, and axiom-free on
  D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-fixed-point-order
             :as fixed-point-order]
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
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-shift-spec
  {:name 'matrix/affine-iterate-shift :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['steps nat]]
    (veq (iterate-affine 'rows 'offset 'steps
                         (affine 'rows 'offset 'initial))
         (iterate-affine 'rows 'offset (succ 'steps) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['initial vector-type] ['steps nat]]
    (let [left-at
          (fn [n]
            (iterate-affine 'rows 'offset n
                            (affine 'rows 'offset 'initial)))
          right-at
          (fn [n]
            (iterate-affine 'rows 'offset (succ n) 'initial))
          motive
          (function/lam [['n nat]] (veq (left-at 'n) (right-at 'n)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (app
            (function/const*
             'matrix/affine-action-respects-values-equivalence [])
            'rows 'offset (left-at 'n) (right-at 'n) 'ih))]
      (prop-nat-rec
       motive
       (app (function/const* 'vector/equivalent-reflexive [])
            (affine 'rows 'offset 'initial))
       step 'steps)))})

(def affine-iterate-subsolution-ascending-spec
  {:name 'matrix/affine-iterate-subsolution-ascending :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['subsolution (vle 'initial (affine 'rows 'offset 'initial))]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset 'steps 'initial)
         (iterate-affine 'rows 'offset (succ 'steps) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['subsolution (vle 'initial (affine 'rows 'offset 'initial))]
     ['steps nat]]
    (let [current (iterate-affine 'rows 'offset 'steps 'initial)
          shifted-start
          (iterate-affine 'rows 'offset 'steps
                          (affine 'rows 'offset 'initial))
          next (iterate-affine 'rows 'offset (succ 'steps) 'initial)
          compare-starts
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset 'initial (affine 'rows 'offset 'initial)
               'rows-positive 'subsolution 'steps)
          shifted-same
          (app (function/const* 'matrix/affine-iterate-shift [])
               'rows 'offset 'initial 'steps)
          shifted-below-next
          (app (function/const* 'vector/equivalent-to-at-most [])
               shifted-start next shifted-same)]
      (at-most-transitive
       current shifted-start next compare-starts shifted-below-next)))})

(def affine-iterate-supersolution-descending-spec
  {:name 'matrix/affine-iterate-supersolution-descending :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['supersolution (vle (affine 'rows 'offset 'initial) 'initial)]
     ['steps nat]]
    (vle (iterate-affine 'rows 'offset (succ 'steps) 'initial)
         (iterate-affine 'rows 'offset 'steps 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['supersolution (vle (affine 'rows 'offset 'initial) 'initial)]
     ['steps nat]]
    (let [shifted-start
          (iterate-affine 'rows 'offset 'steps
                          (affine 'rows 'offset 'initial))
          next (iterate-affine 'rows 'offset (succ 'steps) 'initial)
          current (iterate-affine 'rows 'offset 'steps 'initial)
          shifted-same
          (app (function/const* 'matrix/affine-iterate-shift [])
               'rows 'offset 'initial 'steps)
          shifted-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               shifted-start next shifted-same)
          next-below-shifted
          (app (function/const* 'proposition/right [])
               (vle shifted-start next)
               (vle next shifted-start)
               shifted-bounds)
          compare-starts
          (app (function/const* 'matrix/affine-iterate-monotone-initial [])
               'rows 'offset (affine 'rows 'offset 'initial) 'initial
               'rows-positive 'supersolution 'steps)]
      (at-most-transitive
       next shifted-start current next-below-shifted compare-starts)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-shift-spec
   affine-iterate-subsolution-ascending-spec
   affine-iterate-supersolution-descending-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-fixed-point-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-trajectory-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-trajectory-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
