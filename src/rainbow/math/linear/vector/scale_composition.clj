(ns rainbow.math.linear.vector.scale-composition
  "Composition of uniform nonnegative scaling on native signed vectors.

    scale outer (scale inner values)  ~  scale (outer * inner) values

  The proof maps signed/scale-composition over the list.  Native and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.scale-composition :as signed-composition]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def trivial (function/const* 'proposition/trivial []))

(def scale-composition-spec
  {:name 'vector/scale-composition :universes []
   :type
   (function/forall
    [['outer nnrat] ['inner nnrat] ['values vector-type]]
    (vector-equivalent
     (vector-scale 'outer (vector-scale 'inner 'values))
     (vector-scale
      (app (function/const* 'nnrat/multiply []) 'outer 'inner)
      'values)))
   :value
   (function/lam
    [['outer nnrat] ['inner nnrat] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-scale 'outer (vector-scale 'inner 'current))
            (vector-scale
             (app (function/const* 'nnrat/multiply []) 'outer 'inner)
             'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-composition (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-scale 'outer (signed-scale 'inner 'head))
             (signed-scale
              (app (function/const* 'nnrat/multiply []) 'outer 'inner)
              'head))
            (vector-equivalent
             (vector-scale 'outer (vector-scale 'inner 'tail))
             (vector-scale
              (app (function/const* 'nnrat/multiply []) 'outer 'inner)
              'tail))
            (app (function/const* 'signed/scale-composition [])
                 'outer 'inner 'head)
            'tail-composition))]
      (list-rec motive trivial step 'values)))})

(def definition-specs [])
(def theorem-specs [scale-composition-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.scale-composition rainbow.math.finite.vector rainbow.math.linear.vector.equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-scale-composition theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.scale-composition))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
