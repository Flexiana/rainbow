(ns rainbow.math.linear.matrix.affine-equivalence
  "Congruence and fixed-point invariance for signed affine value iteration.

  Affine action respects matrix, reward-offset, and value equivalence separately
  and jointly.  Nat induction lifts congruence to every finite iterate and shows
  that an affine fixed point remains equivalent to itself after any number of
  iterations.  Theorem-only, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.linear.matrix.affine-iterate :as iterate]
            [rainbow.math.linear.matrix.equivalence :as matrix-equivalence]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.add-order :as add-order]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- prop-nat-rec [m b s n]
  (app (function/const* 'data/Nat.rec [z]) m b s n))
(defn- veq [a b] (app (function/const* 'vector/equivalent []) a b))
(defn- meq [a b] (app (function/const* 'matrix/equivalent []) a b))
(defn- vadd [a b] (app (function/const* 'vector/add []) a b))
(defn- action [rows values]
  (app (function/const* 'matrix/vector-multiply []) rows values))
(defn- affine [rows offset values]
  (app (function/const* 'matrix/affine-action []) rows offset values))
(defn- iterate-affine [rows offset steps initial]
  (app (function/const* 'matrix/affine-iterate [])
       rows offset steps initial))
(defn- vector-reflexive [values]
  (app (function/const* 'vector/equivalent-reflexive []) values))

(def affine-action-respects-offset-equivalence-spec
  {:name 'matrix/affine-action-respects-offset-equivalence :universes []
   :type
   (function/forall
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['values vector-type] ['same (veq 'left 'right)]]
    (veq (affine 'rows 'left 'values)
         (affine 'rows 'right 'values)))
   :value
   (function/lam
    [['rows matrix-type] ['left vector-type] ['right vector-type]
     ['values vector-type] ['same (veq 'left 'right)]]
    (let [image (action 'rows 'values)]
      (app (function/const* 'vector/add-respects-equivalence [])
           'left 'right image image 'same (vector-reflexive image))))})

(def affine-action-respects-values-equivalence-spec
  {:name 'matrix/affine-action-respects-values-equivalence :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['same (veq 'left 'right)]]
    (veq (affine 'rows 'offset 'left)
         (affine 'rows 'offset 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['same (veq 'left 'right)]]
    (app (function/const* 'vector/add-respects-equivalence [])
         'offset 'offset
         (action 'rows 'left) (action 'rows 'right)
         (vector-reflexive 'offset)
         (app
          (function/const* 'matrix/vector-multiply-respects-equivalence [])
          'rows 'left 'right 'same)))})

(def affine-action-respects-rows-equivalence-spec
  {:name 'matrix/affine-action-respects-rows-equivalence :universes []
   :type
   (function/forall
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['same (meq 'left 'right)]]
    (veq (affine 'left 'offset 'values)
         (affine 'right 'offset 'values)))
   :value
   (function/lam
    [['left matrix-type] ['right matrix-type]
     ['offset vector-type] ['values vector-type]
     ['same (meq 'left 'right)]]
    (app (function/const* 'vector/add-respects-equivalence [])
         'offset 'offset
         (action 'left 'values) (action 'right 'values)
         (vector-reflexive 'offset)
         (app
          (function/const*
           'matrix/vector-multiply-respects-matrix-equivalence [])
          'left 'right 'values 'same)))})

(def affine-action-respects-equivalence-spec
  {:name 'matrix/affine-action-respects-equivalence :universes []
   :type
   (function/forall
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left-values vector-type] ['right-values vector-type]
     ['rows-same (meq 'left-rows 'right-rows)]
     ['offset-same (veq 'left-offset 'right-offset)]
     ['values-same (veq 'left-values 'right-values)]]
    (veq (affine 'left-rows 'left-offset 'left-values)
         (affine 'right-rows 'right-offset 'right-values)))
   :value
   (function/lam
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left-values vector-type] ['right-values vector-type]
     ['rows-same (meq 'left-rows 'right-rows)]
     ['offset-same (veq 'left-offset 'right-offset)]
     ['values-same (veq 'left-values 'right-values)]]
    (app (function/const* 'vector/add-respects-equivalence [])
         'left-offset 'right-offset
         (action 'left-rows 'left-values)
         (action 'right-rows 'right-values)
         'offset-same
         (app
          (function/const*
           'matrix/vector-multiply-respects-both-equivalences [])
          'left-rows 'right-rows 'left-values 'right-values
          'rows-same 'values-same)))})

(def affine-iterate-respects-initial-equivalence-spec
  {:name 'matrix/affine-iterate-respects-initial-equivalence :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['same (veq 'left 'right)] ['steps nat]]
    (veq (iterate-affine 'rows 'offset 'steps 'left)
         (iterate-affine 'rows 'offset 'steps 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['same (veq 'left 'right)] ['steps nat]]
    (let [m
          (function/lam
           [['n nat]]
           (veq (iterate-affine 'rows 'offset 'n 'left)
                (iterate-affine 'rows 'offset 'n 'right)))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (app
            (function/const*
             'matrix/affine-action-respects-values-equivalence [])
            'rows 'offset
            (iterate-affine 'rows 'offset 'n 'left)
            (iterate-affine 'rows 'offset 'n 'right)
            'ih))]
      (prop-nat-rec m 'same s 'steps)))})

(def affine-iterate-respects-equivalence-spec
  {:name 'matrix/affine-iterate-respects-equivalence :universes []
   :type
   (function/forall
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left-initial vector-type] ['right-initial vector-type]
     ['rows-same (meq 'left-rows 'right-rows)]
     ['offset-same (veq 'left-offset 'right-offset)]
     ['initial-same (veq 'left-initial 'right-initial)]
     ['steps nat]]
    (veq (iterate-affine 'left-rows 'left-offset 'steps 'left-initial)
         (iterate-affine 'right-rows 'right-offset 'steps 'right-initial)))
   :value
   (function/lam
    [['left-rows matrix-type] ['right-rows matrix-type]
     ['left-offset vector-type] ['right-offset vector-type]
     ['left-initial vector-type] ['right-initial vector-type]
     ['rows-same (meq 'left-rows 'right-rows)]
     ['offset-same (veq 'left-offset 'right-offset)]
     ['initial-same (veq 'left-initial 'right-initial)]
     ['steps nat]]
    (let [left-at
          (fn [n] (iterate-affine 'left-rows 'left-offset n 'left-initial))
          right-at
          (fn [n] (iterate-affine 'right-rows 'right-offset n 'right-initial))
          m
          (function/lam [['n nat]] (veq (left-at 'n) (right-at 'n)))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (app (function/const* 'matrix/affine-action-respects-equivalence [])
                'left-rows 'right-rows 'left-offset 'right-offset
                (left-at 'n) (right-at 'n)
                'rows-same 'offset-same 'ih))]
      (prop-nat-rec m 'initial-same s 'steps)))})

(def affine-iterate-fixed-point-spec
  {:name 'matrix/affine-iterate-fixed-point :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['fixed (veq (affine 'rows 'offset 'value) 'value)]
     ['steps nat]]
    (veq (iterate-affine 'rows 'offset 'steps 'value) 'value))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['value vector-type]
     ['fixed (veq (affine 'rows 'offset 'value) 'value)]
     ['steps nat]]
    (let [at (fn [n] (iterate-affine 'rows 'offset n 'value))
          m (function/lam [['n nat]] (veq (at 'n) 'value))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (app (function/const* 'vector/equivalent-transitive [])
                (affine 'rows 'offset (at 'n))
                (affine 'rows 'offset 'value)
                'value
                (app
                 (function/const*
                  'matrix/affine-action-respects-values-equivalence [])
                 'rows 'offset (at 'n) 'value 'ih)
                'fixed))]
      (prop-nat-rec m (vector-reflexive 'value) s 'steps)))})

(def definition-specs [])
(def theorem-specs
  [affine-action-respects-offset-equivalence-spec
   affine-action-respects-values-equivalence-spec
   affine-action-respects-rows-equivalence-spec
   affine-action-respects-equivalence-spec
   affine-iterate-respects-initial-equivalence-spec
   affine-iterate-respects-equivalence-spec
   affine-iterate-fixed-point-spec])

(defn- extend-spec-if-missing [env milestone spec]
  (if (environment/resolve-id env (:name spec))
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      iterate/extend-environment
      (extend-spec-if-missing
       :vector-add-order add-order/add-respects-equivalence-spec)
      (extend-spec-if-missing
       :finite-matrix-equivalence
       matrix-equivalence/vector-multiply-respects-both-equivalences-spec)
      (support/extend-with :finite-matrix-affine-equivalence theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
