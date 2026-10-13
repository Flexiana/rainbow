(ns rainbow.math.linear.vector.scale-order
  "Nonnegative-rational scaling preserves native positional vector order.

    left <= right  ->  scale c left <= scale c right

  The proof follows the two list shapes carried by vector/at-most.  Matching
  components invoke signed/scale-monotone; mismatched dimensions are already
  false and therefore need no arithmetic.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.vector :as finite-vector]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.scale-order :as signed-scale]
            [rainbow.math.linear.vector.pointwise-order-laws :as order-laws]))

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
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-scale [rate values]
  (app (function/const* 'vector/scale []) rate values))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))
(defn- proposition-left [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- proposition-right [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def trivial (function/const* 'proposition/trivial []))

(def scale-monotone-spec
  {:name 'vector/scale-monotone :universes []
   :type
   (function/forall
    [['rate nnrat] ['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (vector-at-most
     (vector-scale 'rate 'left)
     (vector-scale 'rate 'right)))
   :value
   (function/lam
    [['rate nnrat] ['left vector-type] ['right vector-type]
     ['ordered (vector-at-most 'left 'right)]]
    (let [outer-motive
          (function/lam
           [['current-left vector-type]]
           (function/forall
            [['current-right vector-type]
             ['current-ordered
              (vector-at-most 'current-left 'current-right)]]
            (vector-at-most
             (vector-scale 'rate 'current-left)
             (vector-scale 'rate 'current-right))))
          outer-base
          (let [empty (nil-vector)
                right-motive
                (function/lam
                 [['current-right vector-type]]
                 (function/forall
                  [['current-ordered
                    (vector-at-most empty 'current-right)]]
                  (vector-at-most
                   (vector-scale 'rate empty)
                   (vector-scale 'rate 'current-right))))]
            (function/lam
             [['current-right vector-type]]
             (list-rec
              right-motive
              (function/lam
               [['current-ordered (vector-at-most empty empty)]]
               trivial)
              (function/lam
               [['right-head signed] ['right-tail vector-type]
                ['ignored (app right-motive 'right-tail)]]
               (function/lam
                [['current-ordered
                  (vector-at-most
                   empty (cons-vector 'right-head 'right-tail))]]
                'current-ordered))
              'current-right)))
          outer-step
          (function/lam
           [['left-head signed] ['left-tail vector-type]
            ['tail-monotone (app outer-motive 'left-tail)]]
           (let [current-left (cons-vector 'left-head 'left-tail)
                 right-motive
                 (function/lam
                  [['current-right vector-type]]
                  (function/forall
                   [['current-ordered
                     (vector-at-most current-left 'current-right)]]
                   (vector-at-most
                    (vector-scale 'rate current-left)
                    (vector-scale 'rate 'current-right))))]
             (function/lam
              [['current-right vector-type]]
              (list-rec
               right-motive
               (function/lam
                [['current-ordered
                  (vector-at-most current-left (nil-vector))]]
                'current-ordered)
               (function/lam
                [['right-head signed] ['right-tail vector-type]
                 ['ignored (app right-motive 'right-tail)]]
                (function/lam
                 [['current-ordered
                   (vector-at-most
                    current-left (cons-vector 'right-head 'right-tail))]]
                 (let [head-order (signed-at-most 'left-head 'right-head)
                       tail-order (vector-at-most 'left-tail 'right-tail)]
                   (conjoin
                    (signed-at-most
                     (app (function/const* 'signed/scale [])
                          'rate 'left-head)
                     (app (function/const* 'signed/scale [])
                          'rate 'right-head))
                    (vector-at-most
                     (vector-scale 'rate 'left-tail)
                     (vector-scale 'rate 'right-tail))
                    (app (function/const* 'signed/scale-monotone [])
                         'rate 'left-head 'right-head
                         (proposition-left
                          head-order tail-order 'current-ordered))
                    (app 'tail-monotone 'right-tail
                         (proposition-right
                          head-order tail-order 'current-ordered))))))
               'current-right))))]
      (app (list-rec outer-motive outer-base outer-step 'left)
           'right 'ordered)))})

(def scale-respects-equivalence-spec
  {:name 'vector/scale-respects-equivalence :universes []
   :type
   (function/forall
    [['rate nnrat] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (vector-equivalent
     (vector-scale 'rate 'left)
     (vector-scale 'rate 'right)))
   :value
   (function/lam
    [['rate nnrat] ['left vector-type] ['right vector-type]
     ['same (vector-equivalent 'left 'right)]]
    (let [bounds
          (app (function/const* 'vector/equivalent-to-mutual-at-most [])
               'left 'right 'same)
          forward
          (proposition-left
           (vector-at-most 'left 'right)
           (vector-at-most 'right 'left)
           bounds)
          backward
          (proposition-right
           (vector-at-most 'left 'right)
           (vector-at-most 'right 'left)
           bounds)]
      (app (function/const* 'vector/at-most-antisymmetric [])
           (vector-scale 'rate 'left)
           (vector-scale 'rate 'right)
           (app (function/const* 'vector/scale-monotone [])
                'rate 'left 'right forward)
           (app (function/const* 'vector/scale-monotone [])
                'rate 'right 'left backward))))})

(def definition-specs [])
(def theorem-specs
  [scale-monotone-spec scale-respects-equivalence-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.scale-order rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :vector-scale-order theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.scale-order))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
