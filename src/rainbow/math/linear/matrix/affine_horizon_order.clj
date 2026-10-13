(ns rainbow.math.linear.matrix.affine-horizon-order
  "Composition and arbitrary-horizon order for finite affine iteration.

  Natural addition recurses on the extra-horizon argument, so affine iteration
  forms a finite semigroup action: running `base` steps and then `extra` steps
  agrees with running `extra + base` steps.  Bellman subsolutions therefore
  stay below every later iterate, while supersolutions stay above every later
  iterate.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-trajectory-order
             :as trajectory-order]
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
(defn- nadd [left right]
  (app (function/const* 'algebra/nat-add []) left right))
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
(defn- vector-reflexive [values]
  (app (function/const* 'vector/equivalent-reflexive []) values))
(defn- at-most-reflexive [values]
  (app (function/const* 'vector/equivalent-to-at-most [])
       values values (vector-reflexive values)))
(defn- at-most-transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/at-most-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-add-spec
  {:name 'matrix/affine-iterate-add :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['extra nat] ['base nat]]
    (veq (iterate-affine 'rows 'offset (nadd 'extra 'base) 'initial)
         (iterate-affine
          'rows 'offset 'extra
          (iterate-affine 'rows 'offset 'base 'initial))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['extra nat] ['base nat]]
    (let [left-at
          (fn [n]
            (iterate-affine 'rows 'offset (nadd n 'base) 'initial))
          base-result
          (iterate-affine 'rows 'offset 'base 'initial)
          right-at
          (fn [n]
            (iterate-affine 'rows 'offset n base-result))
          motive
          (function/lam [['n nat]] (veq (left-at 'n) (right-at 'n)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (app
            (function/const*
             'matrix/affine-action-respects-values-equivalence [])
            'rows 'offset (left-at 'n) (right-at 'n) 'ih))]
      (prop-nat-rec motive (vector-reflexive base-result) step 'extra)))})

(def affine-iterate-subsolution-horizon-spec
  {:name 'matrix/affine-iterate-subsolution-horizon :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['subsolution (vle 'initial (affine 'rows 'offset 'initial))]
     ['base nat] ['extra nat]]
    (vle (iterate-affine 'rows 'offset 'base 'initial)
         (iterate-affine 'rows 'offset (nadd 'extra 'base) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['subsolution (vle 'initial (affine 'rows 'offset 'initial))]
     ['base nat] ['extra nat]]
    (let [origin (iterate-affine 'rows 'offset 'base 'initial)
          at (fn [n]
               (iterate-affine 'rows 'offset (nadd n 'base) 'initial))
          motive (function/lam [['n nat]] (vle origin (at 'n)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (at-most-transitive
            origin (at 'n) (at (succ 'n))
            'ih
            (app
             (function/const*
              'matrix/affine-iterate-subsolution-ascending [])
             'rows 'offset 'initial 'rows-positive 'subsolution
             (nadd 'n 'base))))]
      (prop-nat-rec motive (at-most-reflexive origin) step 'extra)))})

(def affine-iterate-supersolution-horizon-spec
  {:name 'matrix/affine-iterate-supersolution-horizon :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['supersolution (vle (affine 'rows 'offset 'initial) 'initial)]
     ['base nat] ['extra nat]]
    (vle (iterate-affine 'rows 'offset (nadd 'extra 'base) 'initial)
         (iterate-affine 'rows 'offset 'base 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['supersolution (vle (affine 'rows 'offset 'initial) 'initial)]
     ['base nat] ['extra nat]]
    (let [origin (iterate-affine 'rows 'offset 'base 'initial)
          at (fn [n]
               (iterate-affine 'rows 'offset (nadd n 'base) 'initial))
          motive (function/lam [['n nat]] (vle (at 'n) origin))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (at-most-transitive
            (at (succ 'n)) (at 'n) origin
            (app
             (function/const*
              'matrix/affine-iterate-supersolution-descending [])
             'rows 'offset 'initial 'rows-positive 'supersolution
             (nadd 'n 'base))
            'ih))]
      (prop-nat-rec motive (at-most-reflexive origin) step 'extra)))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-add-spec
   affine-iterate-subsolution-horizon-spec
   affine-iterate-supersolution-horizon-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-trajectory-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-horizon-order theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-horizon-order))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
