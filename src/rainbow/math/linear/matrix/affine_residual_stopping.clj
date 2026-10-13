(ns rainbow.math.linear.matrix.affine-residual-stopping
  "Exact residual stopping certificates for finite affine value iteration.

  At any finite step, consecutive iterate equivalence is equivalent to the
  current linear residual equation `x - rows*x ~ offset`, under the explicit
  shape premises required by truncating vector subtraction.  This connects an
  observable value-iteration stopping condition directly to the policy-
  evaluation equation.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-residual :as residual]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app successor n))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- same-shape [a b]
  (app (function/const* 'vector/same-shape []) a b))
(defn- vsub [a b] (app (function/const* 'vector/subtract []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right left-middle middle-right))

(def affine-iterate-stable-implies-residual-equation-spec
  {:name 'matrix/affine-iterate-stable-implies-residual-equation :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['offset-image-shape
      (same-shape
       'offset
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)]
      (veq (vsub current (action 'rows current)) 'offset)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['offset-image-shape
      (same-shape
       'offset
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['stable
      (veq (iterate-affine 'rows 'offset 'base 'initial)
           (iterate-affine 'rows 'offset (succ 'base) 'initial))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          fixed
          (app
           (function/const*
            'matrix/affine-iterate-stable-implies-fixed-point [])
           'rows 'offset 'initial 'base 'stable)]
      (app
       (function/const*
        'matrix/affine-fixed-point-implies-residual-equation [])
       'rows 'offset current 'offset-image-shape fixed)))})

(def affine-iterate-residual-equation-implies-stable-spec
  {:name 'matrix/affine-iterate-residual-equation-implies-stable :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['value-image-shape
      (same-shape
       (iterate-affine 'rows 'offset 'base 'initial)
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['residual-equation
      (let [current (iterate-affine 'rows 'offset 'base 'initial)]
        (veq (vsub current (action 'rows current)) 'offset))]]
    (veq (iterate-affine 'rows 'offset 'base 'initial)
         (iterate-affine 'rows 'offset (succ 'base) 'initial)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['value-image-shape
      (same-shape
       (iterate-affine 'rows 'offset 'base 'initial)
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['residual-equation
      (let [current (iterate-affine 'rows 'offset 'base 'initial)]
        (veq (vsub current (action 'rows current)) 'offset))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          next (iterate-affine 'rows 'offset (succ 'base) 'initial)
          image (affine 'rows 'offset current)
          fixed
          (app
           (function/const*
            'matrix/affine-residual-equation-implies-fixed-point [])
           'rows 'offset current 'value-image-shape
           'residual-equation)
          successor-unfold
          (app (function/const* 'matrix/affine-iterate-successor [])
               'rows 'offset 'base 'initial)
          next-current
          (transitive next image current successor-unfold fixed)]
      (symmetric next current next-current)))})

(def affine-iterate-stable-iff-residual-equation-spec
  {:name 'matrix/affine-iterate-stable-iff-residual-equation :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['offset-image-shape
      (same-shape
       'offset
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['value-image-shape
      (same-shape
       (iterate-affine 'rows 'offset 'base 'initial)
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          stable-prop
          (veq current
               (iterate-affine 'rows 'offset (succ 'base) 'initial))
          residual-prop
          (veq (vsub current (action 'rows current)) 'offset)]
      (proposition/equivalence stable-prop residual-prop)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['base nat]
     ['offset-image-shape
      (same-shape
       'offset
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]
     ['value-image-shape
      (same-shape
       (iterate-affine 'rows 'offset 'base 'initial)
       (action 'rows (iterate-affine 'rows 'offset 'base 'initial)))]]
    (let [current (iterate-affine 'rows 'offset 'base 'initial)
          stable-prop
          (veq current
               (iterate-affine 'rows 'offset (succ 'base) 'initial))
          residual-prop
          (veq (vsub current (action 'rows current)) 'offset)]
      (app
       (function/const* 'proposition/equivalence-intro [])
       stable-prop residual-prop
       (function/lam
        [['stable stable-prop]]
        (app
         (function/const*
          'matrix/affine-iterate-stable-implies-residual-equation [])
         'rows 'offset 'initial 'base 'offset-image-shape 'stable))
       (function/lam
        [['residual-equation residual-prop]]
        (app
         (function/const*
          'matrix/affine-iterate-residual-equation-implies-stable [])
         'rows 'offset 'initial 'base 'value-image-shape
         'residual-equation)))))})

(def definition-specs [])
(def theorem-specs
  [affine-iterate-stable-implies-residual-equation-spec
   affine-iterate-residual-equation-implies-stable-spec
   affine-iterate-stable-iff-residual-equation-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-residual])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-residual-stopping theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-residual-stopping))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
