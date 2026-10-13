(ns rainbow.math.linear.vector.convex-combination
  "Normalized two-point convex combinations preserve vector intervals."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.distributive :as distributive]
            [rainbow.math.rational.signed.scale-order :as signed-scale]
            [rainbow.math.linear.vector.add-order :as add-order]
            [rainbow.math.linear.vector.equivalence-transitivity :as equivalence-transitivity]
            [rainbow.math.linear.vector.scale-order :as scale-order]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def trivial (function/const* 'proposition/trivial []))

(defn- app [f & args]
  (apply function/app f args))

(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))

(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))

(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))

(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))

(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))

(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))

(defn- positive [value]
  (app (function/const* 'signed/positive []) value))

(defn- negative [value]
  (app (function/const* 'signed/negative []) value))

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

(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))

(defn- wsum2 [w0 w1 left right]
  (app (function/const* 'vector/nnrat-wsum2 [])
       w0 w1 left right))

(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))

(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))

(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def wsum2-spec
  {:name 'vector/nnrat-wsum2
   :kind :definition
   :universes []
   :type (function/arrow nnrat nnrat vector-type vector-type vector-type)
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat]
     ['left vector-type] ['right vector-type]]
    (vector-add (vector-scale 'w0 'left)
                (vector-scale 'w1 'right)))})

(def signed-scale-additive-rate-spec
  {:name 'signed/scale-additive-rate
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat] ['value signed]]
    (signed-equivalent
     (signed-add (signed-scale 'w0 'value)
                 (signed-scale 'w1 'value))
     (signed-scale (radd 'w0 'w1) 'value)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['value signed]]
    (let [sum-rate (radd 'w0 'w1)
          sum-positive
          (radd (rmul 'w0 (positive 'value))
                (rmul 'w1 (positive 'value)))
          sum-negative
          (radd (rmul 'w0 (negative 'value))
                (rmul 'w1 (negative 'value)))
          scaled-positive (rmul sum-rate (positive 'value))
          scaled-negative (rmul sum-rate (negative 'value))
          positive-distributed
          (app (function/const* 'nnrat/multiply-distributes-add-right [])
               'w0 'w1 (positive 'value))
          negative-distributed
          (app (function/const* 'nnrat/multiply-distributes-add-right [])
               'w0 'w1 (negative 'value))]
      (app
       (function/const* 'nnrat/add-respects-equivalence [])
       sum-positive scaled-positive
       scaled-negative sum-negative
       (app (function/const* 'nnrat/equivalent-symmetric [])
            scaled-positive sum-positive positive-distributed)
       negative-distributed)))})

(def signed-scale-one-spec
  {:name 'signed/scale-one
   :universes []
   :type
   (function/forall
    [['value signed]]
    (signed-equivalent (signed-scale nnrat-one 'value) 'value))
   :value
   (function/lam
    [['value signed]]
    (let [scaled-positive (rmul nnrat-one (positive 'value))
          scaled-negative (rmul nnrat-one (negative 'value))
          positive-one
          (app (function/const* 'nnrat/multiply-one-left [])
               (positive 'value))
          negative-one
          (app (function/const* 'nnrat/multiply-one-left [])
               (negative 'value))]
      (app
       (function/const* 'nnrat/add-respects-equivalence [])
       scaled-positive (positive 'value)
       (negative 'value) scaled-negative
       positive-one
       (app (function/const* 'nnrat/equivalent-symmetric [])
            scaled-negative (negative 'value) negative-one))))})

(def signed-scale-respects-rate-equivalence-spec
  {:name 'signed/scale-respects-rate-equivalence
   :universes []
   :type
   (function/forall
    [['left-rate nnrat] ['right-rate nnrat] ['value signed]
     ['same-rate (rat-equivalent 'left-rate 'right-rate)]]
    (signed-equivalent
     (signed-scale 'left-rate 'value)
     (signed-scale 'right-rate 'value)))
   :value
   (function/lam
    [['left-rate nnrat] ['right-rate nnrat] ['value signed]
     ['same-rate (rat-equivalent 'left-rate 'right-rate)]]
    (let [left-positive (rmul 'left-rate (positive 'value))
          right-positive (rmul 'right-rate (positive 'value))
          left-negative (rmul 'left-rate (negative 'value))
          right-negative (rmul 'right-rate (negative 'value))
          positive-same
          (app
           (function/const* 'nnrat/multiply-respects-equivalence [])
           'left-rate 'right-rate
           (positive 'value) (positive 'value)
           'same-rate
           (app (function/const* 'nnrat/equivalent-reflexive [])
                (positive 'value)))
          negative-same
          (app
           (function/const* 'nnrat/multiply-respects-equivalence [])
           'left-rate 'right-rate
           (negative 'value) (negative 'value)
           'same-rate
           (app (function/const* 'nnrat/equivalent-reflexive [])
                (negative 'value)))]
      (app
       (function/const* 'nnrat/add-respects-equivalence [])
       left-positive right-positive
       right-negative left-negative
       positive-same
       (app (function/const* 'nnrat/equivalent-symmetric [])
            left-negative right-negative negative-same))))})

(def vector-scale-additive-rate-spec
  {:name 'vector/scale-additive-rate
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat] ['values vector-type]]
    (vector-equivalent
     (vector-add (vector-scale 'w0 'values)
                 (vector-scale 'w1 'values))
     (vector-scale (radd 'w0 'w1) 'values)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-add (vector-scale 'w0 'current)
                        (vector-scale 'w1 'current))
            (vector-scale (radd 'w0 'w1) 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-same (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-add (signed-scale 'w0 'head)
                         (signed-scale 'w1 'head))
             (signed-scale (radd 'w0 'w1) 'head))
            (vector-equivalent
             (vector-add (vector-scale 'w0 'tail)
                         (vector-scale 'w1 'tail))
             (vector-scale (radd 'w0 'w1) 'tail))
            (app (function/const* 'signed/scale-additive-rate [])
                 'w0 'w1 'head)
            'tail-same))]
      (list-rec motive trivial step 'values)))})

(def vector-scale-one-spec
  {:name 'vector/scale-one
   :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent (vector-scale nnrat-one 'values) 'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent (vector-scale nnrat-one 'current) 'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-same (app motive 'tail)]]
           (conjoin
            (signed-equivalent (signed-scale nnrat-one 'head) 'head)
            (vector-equivalent (vector-scale nnrat-one 'tail) 'tail)
            (app (function/const* 'signed/scale-one []) 'head)
            'tail-same))]
      (list-rec motive trivial step 'values)))})

(def vector-scale-respects-rate-equivalence-spec
  {:name 'vector/scale-respects-rate-equivalence
   :universes []
   :type
   (function/forall
    [['left-rate nnrat] ['right-rate nnrat]
     ['values vector-type]
     ['same-rate (rat-equivalent 'left-rate 'right-rate)]]
    (vector-equivalent
     (vector-scale 'left-rate 'values)
     (vector-scale 'right-rate 'values)))
   :value
   (function/lam
    [['left-rate nnrat] ['right-rate nnrat]
     ['values vector-type]
     ['same-rate (rat-equivalent 'left-rate 'right-rate)]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-scale 'left-rate 'current)
            (vector-scale 'right-rate 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-same (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-scale 'left-rate 'head)
             (signed-scale 'right-rate 'head))
            (vector-equivalent
             (vector-scale 'left-rate 'tail)
             (vector-scale 'right-rate 'tail))
            (app
             (function/const* 'signed/scale-respects-rate-equivalence [])
             'left-rate 'right-rate 'head 'same-rate)
            'tail-same))]
      (list-rec motive trivial step 'values)))})

(def wsum2-monotone-spec
  {:name 'vector/nnrat-wsum2-monotone
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat]
     ['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (vector-at-most
     (wsum2 'w0 'w1 'left 'right)
     (wsum2 'w0 'w1 'left-prime 'right-prime)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat]
     ['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (app
     (function/const* 'vector/add-monotone [])
     (vector-scale 'w0 'left) (vector-scale 'w0 'left-prime)
     (vector-scale 'w1 'right) (vector-scale 'w1 'right-prime)
     (app (function/const* 'vector/scale-monotone [])
          'w0 'left 'left-prime 'left-ordered)
     (app (function/const* 'vector/scale-monotone [])
          'w1 'right 'right-prime 'right-ordered)))})

(def wsum2-normalized-repeated-spec
  {:name 'vector/nnrat-wsum2-normalized-repeated
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat] ['values vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]]
    (vector-equivalent
     (wsum2 'w0 'w1 'values 'values)
     'values))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['values vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]]
    (let [weighted (wsum2 'w0 'w1 'values 'values)
          summed (vector-scale (radd 'w0 'w1) 'values)
          unit-scaled (vector-scale nnrat-one 'values)
          weighted-summed
          (app (function/const* 'vector/scale-additive-rate [])
               'w0 'w1 'values)
          summed-unit
          (app
           (function/const* 'vector/scale-respects-rate-equivalence [])
           (radd 'w0 'w1) nnrat-one 'values 'normalized)
          unit-values
          (app (function/const* 'vector/scale-one []) 'values)]
      (app
       (function/const* 'vector/equivalent-transitive [])
       weighted summed 'values weighted-summed
       (app
        (function/const* 'vector/equivalent-transitive [])
        summed unit-scaled 'values summed-unit unit-values))))})

(def convex-lower-bound-spec
  {:name 'vector/nnrat-convex-lower-bound
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat]
     ['lower vector-type] ['left vector-type] ['right vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]
     ['lower-left (vector-at-most 'lower 'left)]
     ['lower-right (vector-at-most 'lower 'right)]]
    (vector-at-most 'lower (wsum2 'w0 'w1 'left 'right)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat]
     ['lower vector-type] ['left vector-type] ['right vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]
     ['lower-left (vector-at-most 'lower 'left)]
     ['lower-right (vector-at-most 'lower 'right)]]
    (let [weighted-lower (wsum2 'w0 'w1 'lower 'lower)
          weighted (wsum2 'w0 'w1 'left 'right)
          repeated-same
          (app
           (function/const* 'vector/nnrat-wsum2-normalized-repeated [])
           'w0 'w1 'lower 'normalized)
          repeated-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               weighted-lower 'lower repeated-same)
          lower-to-weighted-lower
          (proposition-right
           (vector-at-most weighted-lower 'lower)
           (vector-at-most 'lower weighted-lower)
           repeated-bounds)
          weighted-monotone
          (app (function/const* 'vector/nnrat-wsum2-monotone [])
               'w0 'w1 'lower 'left 'lower 'right
               'lower-left 'lower-right)]
      (app (function/const* 'vector/at-most-transitive [])
           'lower weighted-lower weighted
           lower-to-weighted-lower weighted-monotone)))})

(def convex-upper-bound-spec
  {:name 'vector/nnrat-convex-upper-bound
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat]
     ['left vector-type] ['right vector-type] ['upper vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]
     ['left-upper (vector-at-most 'left 'upper)]
     ['right-upper (vector-at-most 'right 'upper)]]
    (vector-at-most (wsum2 'w0 'w1 'left 'right) 'upper))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat]
     ['left vector-type] ['right vector-type] ['upper vector-type]
     ['normalized (rat-equivalent (radd 'w0 'w1) nnrat-one)]
     ['left-upper (vector-at-most 'left 'upper)]
     ['right-upper (vector-at-most 'right 'upper)]]
    (let [weighted (wsum2 'w0 'w1 'left 'right)
          weighted-upper (wsum2 'w0 'w1 'upper 'upper)
          weighted-monotone
          (app (function/const* 'vector/nnrat-wsum2-monotone [])
               'w0 'w1 'left 'upper 'right 'upper
               'left-upper 'right-upper)
          repeated-same
          (app
           (function/const* 'vector/nnrat-wsum2-normalized-repeated [])
           'w0 'w1 'upper 'normalized)
          repeated-bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               weighted-upper 'upper repeated-same)
          weighted-upper-to-upper
          (proposition-left
           (vector-at-most weighted-upper 'upper)
           (vector-at-most 'upper weighted-upper)
           repeated-bounds)]
      (app (function/const* 'vector/at-most-transitive [])
           weighted weighted-upper 'upper
           weighted-monotone weighted-upper-to-upper)))})

(def definition-specs [wsum2-spec])

(def theorem-specs
  [signed-scale-additive-rate-spec
   signed-scale-one-spec
   signed-scale-respects-rate-equivalence-spec
   vector-scale-additive-rate-spec
   vector-scale-one-spec
   vector-scale-respects-rate-equivalence-spec
   wsum2-monotone-spec
   wsum2-normalized-repeated-spec
   convex-lower-bound-spec
   convex-upper-bound-spec])

(defn- extend-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (if (environment/resolve-id current (:name spec))
       current
       (support/extend-with current milestone [spec])))
   checked-environment
   specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.add-order rainbow.math.rational.signed.scale-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-if-missing :nnrat-distributive [distributive/multiply-one-left-spec]) (extend-if-missing :vector-scale-order scale-order/theorem-specs) (extend-if-missing :vector-equivalence-transitivity equivalence-transitivity/theorem-specs) (support/extend-with :vector-convex-combination (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.convex-combination))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
