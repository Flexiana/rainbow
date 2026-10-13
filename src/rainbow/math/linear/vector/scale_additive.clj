(ns rainbow.math.linear.vector.scale-additive
  "Uniform nonnegative scaling distributes over native vector addition.

    scale c (left + right)  ~  scale c left + scale c right

  Vector addition truncates to the shorter list, and both sides truncate at the
  same position.  The cons/cons case invokes signed/scale-additive and the tail
  induction hypothesis.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.scale-additive :as signed-additive]
            [rainbow.math.linear.vector.equivalence :as vector-equivalence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-scale [rate value]
  (app (function/const* 'signed/scale []) rate value))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
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

(def scale-additive-spec
  {:name 'vector/scale-additive :universes []
   :type
   (function/forall
    [['rate nnrat] ['left vector-type] ['right vector-type]]
    (vector-equivalent
     (vector-scale 'rate (vector-add 'left 'right))
     (vector-add
      (vector-scale 'rate 'left)
      (vector-scale 'rate 'right))))
   :value
   (function/lam
    [['rate nnrat] ['left vector-type] ['right vector-type]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]]
            (vector-equivalent
             (vector-scale
              'rate (vector-add 'current-left 'current-right))
             (vector-add
              (vector-scale 'rate 'current-left)
              (vector-scale 'rate 'current-right)))))
          outer-base
          (function/lam
           [['current-right vector-type]]
           trivial)
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-additive (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (vector-equivalent
                   (vector-scale
                    'rate (vector-add current-left 'current-right))
                   (vector-add
                    (vector-scale 'rate current-left)
                    (vector-scale 'rate 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               trivial
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (conjoin
                 (signed-equivalent
                  (signed-scale
                   'rate (signed-add 'left-head 'right-head))
                  (signed-add
                   (signed-scale 'rate 'left-head)
                   (signed-scale 'rate 'right-head)))
                 (vector-equivalent
                  (vector-scale
                   'rate (vector-add 'left-tail 'right-tail))
                  (vector-add
                   (vector-scale 'rate 'left-tail)
                   (vector-scale 'rate 'right-tail)))
                 (app (function/const* 'signed/scale-additive [])
                      'rate 'left-head 'right-head)
                 (app 'tail-additive 'right-tail)))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right)))})

(def definition-specs [])
(def theorem-specs [scale-additive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.scale-additive rainbow.math.finite.vector rainbow.math.linear.vector.equivalence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-scale-additive theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.scale-additive))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
