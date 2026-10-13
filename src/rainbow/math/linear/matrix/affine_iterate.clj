(ns rainbow.math.linear.matrix.affine-iterate
  "Finite signed value iteration for affine matrix maps.

  `matrix/affine-iterate` repeatedly applies `offset + rows·value`.  Its native
  Nat recursor equations, nonnegative-cone invariant, monotonicity in the
  initial value, and simultaneous data/initial monotonicity are ordinary proof
  data.  The all-parameter theorem carries the exact source/destination cone
  premises required at every induction step.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.linear.matrix.affine-sign :as affine-sign]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def z [:zero])
(def t [:succ z])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type (function/app (function/const* 'data/List [t]) signed))
(def matrix-type (function/app (function/const* 'data/List [t]) vector-type))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app successor n))
(defn- nat-rec [m b s n]
  (app (function/const* 'data/Nat.rec [t]) m b s n))
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

(def affine-iterate-spec
  {:name 'matrix/affine-iterate :kind :definition :universes []
   :type (function/arrow matrix-type vector-type nat vector-type vector-type)
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['steps nat] ['initial vector-type]]
    (nat-rec
     (function/lam [['ignored nat]] vector-type)
     'initial
     (function/lam
      [['ignored-step nat] ['previous vector-type]]
      (affine 'rows 'offset 'previous))
     'steps))})

(def affine-iterate-zero-spec
  {:name 'matrix/affine-iterate-zero :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]]
    (veq (iterate-affine 'rows 'offset zero 'initial) 'initial))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]]
    (app (function/const* 'vector/equivalent-reflexive []) 'initial))})

(def affine-iterate-successor-spec
  {:name 'matrix/affine-iterate-successor :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['steps nat] ['initial vector-type]]
    (veq (iterate-affine 'rows 'offset (succ 'steps) 'initial)
         (affine 'rows 'offset
                 (iterate-affine 'rows 'offset 'steps 'initial))))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['steps nat] ['initial vector-type]]
    (app
     (function/const* 'vector/equivalent-reflexive [])
     (affine 'rows 'offset
             (iterate-affine 'rows 'offset 'steps 'initial))))})

(def affine-iterate-nonnegative-spec
  {:name 'matrix/affine-iterate-nonnegative :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['offset-positive (vle (vz 'offset) 'offset)]
     ['initial-positive (vle (vz 'initial) 'initial)]
     ['steps nat]]
    (let [result (iterate-affine 'rows 'offset 'steps 'initial)]
      (vle (vz result) result)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type] ['initial vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['offset-positive (vle (vz 'offset) 'offset)]
     ['initial-positive (vle (vz 'initial) 'initial)]
     ['steps nat]]
    (let [m
          (function/lam
           [['n nat]]
           (let [result (iterate-affine 'rows 'offset 'n 'initial)]
             (vle (vz result) result)))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (app (function/const* 'matrix/affine-action-nonnegative [])
                'rows 'offset
                (iterate-affine 'rows 'offset 'n 'initial)
                'offset-positive 'rows-positive 'ih))]
      (prop-nat-rec m 'initial-positive s 'steps)))})

(def affine-iterate-monotone-initial-spec
  {:name 'matrix/affine-iterate-monotone-initial :universes []
   :type
   (function/forall
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['ordered (vle 'left 'right)] ['steps nat]]
    (vle (iterate-affine 'rows 'offset 'steps 'left)
         (iterate-affine 'rows 'offset 'steps 'right)))
   :value
   (function/lam
    [['rows matrix-type] ['offset vector-type]
     ['left vector-type] ['right vector-type]
     ['rows-positive (mle (mz 'rows) 'rows)]
     ['ordered (vle 'left 'right)] ['steps nat]]
    (let [m
          (function/lam
           [['n nat]]
           (vle (iterate-affine 'rows 'offset 'n 'left)
                (iterate-affine 'rows 'offset 'n 'right)))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (app (function/const* 'matrix/affine-action-monotone-values [])
                'rows 'offset
                (iterate-affine 'rows 'offset 'n 'left)
                (iterate-affine 'rows 'offset 'n 'right)
                'rows-positive 'ih))]
      (prop-nat-rec m 'ordered s 'steps)))})

(def affine-iterate-monotone-all-spec
  {:name 'matrix/affine-iterate-monotone-all :universes []
   :type
   (function/forall
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-initial vector-type] ['destination-initial vector-type]
     ['source-rows-positive
      (mle (mz 'source-rows) 'source-rows)]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-offset-positive
      (vle (vz 'source-offset) 'source-offset)]
     ['source-initial-positive
      (vle (vz 'source-initial) 'source-initial)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['initial-ordered (vle 'source-initial 'destination-initial)]
     ['steps nat]]
    (vle (iterate-affine 'source-rows 'source-offset
                         'steps 'source-initial)
         (iterate-affine 'destination-rows 'destination-offset
                         'steps 'destination-initial)))
   :value
   (function/lam
    [['source-rows matrix-type] ['destination-rows matrix-type]
     ['source-offset vector-type] ['destination-offset vector-type]
     ['source-initial vector-type] ['destination-initial vector-type]
     ['source-rows-positive
      (mle (mz 'source-rows) 'source-rows)]
     ['destination-rows-positive
      (mle (mz 'destination-rows) 'destination-rows)]
     ['source-offset-positive
      (vle (vz 'source-offset) 'source-offset)]
     ['source-initial-positive
      (vle (vz 'source-initial) 'source-initial)]
     ['rows-ordered (mle 'source-rows 'destination-rows)]
     ['offset-ordered (vle 'source-offset 'destination-offset)]
     ['initial-ordered (vle 'source-initial 'destination-initial)]
     ['steps nat]]
    (let [source-at
          (fn [n]
            (iterate-affine 'source-rows 'source-offset n 'source-initial))
          destination-at
          (fn [n]
            (iterate-affine 'destination-rows 'destination-offset
                            n 'destination-initial))
          m
          (function/lam
           [['n nat]]
           (vle (source-at 'n) (destination-at 'n)))
          s
          (function/lam
           [['n nat] ['ih (app m 'n)]]
           (let [source-positive
                 (app
                  (function/const* 'matrix/affine-iterate-nonnegative [])
                  'source-rows 'source-offset 'source-initial
                  'source-rows-positive 'source-offset-positive
                  'source-initial-positive 'n)]
             (app (function/const* 'matrix/affine-action-monotone-all [])
                  'source-rows 'destination-rows
                  'source-offset 'destination-offset
                  (source-at 'n) (destination-at 'n)
                  'destination-rows-positive source-positive
                  'rows-ordered 'offset-ordered 'ih)))]
      (prop-nat-rec m 'initial-ordered s 'steps)))})

(def definition-specs [affine-iterate-spec])
(def theorem-specs
  [affine-iterate-zero-spec
   affine-iterate-successor-spec
   affine-iterate-nonnegative-spec
   affine-iterate-monotone-initial-spec
   affine-iterate-monotone-all-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.matrix.affine-sign])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-matrix-affine-iterate (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.linear.matrix.affine-iterate))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
