(ns rainbow.math.linear.vector.shape-map
  "Componentwise maps preserve native vector shape.

  The general theorem covers every signed-to-signed component mapping.  Native
  vector negation, uniform scaling, and zero-like construction are reducible
  specializations.  The proof is one List induction whose head obligation is
  signed zero reflexivity.  Native and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.shape-cancellation :as shape]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- list-map [mapping values]
  (app (function/const* 'list/map [type-level type-level])
       signed signed mapping values))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- same-shape [left right]
  (app (function/const* 'vector/same-shape []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def trivial (function/const* 'proposition/trivial []))

(def map-preserves-shape-spec
  {:name 'vector/map-preserves-shape :universes []
   :type
   (function/forall
    [['mapping (function/arrow signed signed)]
     ['values vector-type]]
    (same-shape (list-map 'mapping 'values) 'values))
   :value
   (function/lam
    [['mapping (function/arrow signed signed)]
     ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (same-shape (list-map 'mapping 'current) 'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-shape (app motive 'tail)]]
           (conjoin
            (signed-equivalent signed-zero signed-zero)
            (vector-equivalent
             (zero-like (list-map 'mapping 'tail))
             (zero-like 'tail))
            (app (function/const* 'signed/equivalent-reflexive [])
                 signed-zero)
            'tail-shape))]
      (list-rec motive trivial step 'values)))})

(def negate-preserves-shape-spec
  {:name 'vector/negate-preserves-shape :universes []
   :type
   (function/forall
    [['values vector-type]]
    (same-shape (vector-negate 'values) 'values))
   :value
   (function/lam
    [['values vector-type]]
    (app
     (function/const* 'vector/map-preserves-shape [])
     (function/lam [['value signed]] (signed-negate 'value))
     'values))})

(def scale-preserves-shape-spec
  {:name 'vector/scale-preserves-shape :universes []
   :type
   (function/forall
    [['rate nnrat] ['values vector-type]]
    (same-shape (vector-scale 'rate 'values) 'values))
   :value
   (function/lam
    [['rate nnrat] ['values vector-type]]
    (app
     (function/const* 'vector/map-preserves-shape [])
     (function/lam [['value signed]] (signed-scale 'rate 'value))
     'values))})

(def zero-like-preserves-shape-spec
  {:name 'vector/zero-like-preserves-shape :universes []
   :type
   (function/forall
    [['values vector-type]]
    (same-shape (zero-like 'values) 'values))
   :value
   (function/lam
    [['values vector-type]]
    (app
     (function/const* 'vector/map-preserves-shape [])
     (function/lam [['ignored signed]] signed-zero)
     'values))})

(def definition-specs [])
(def theorem-specs
  [map-preserves-shape-spec
   negate-preserves-shape-spec
   scale-preserves-shape-spec
   zero-like-preserves-shape-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      shape/extend-environment
      (support/extend-with :vector-shape-map theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
