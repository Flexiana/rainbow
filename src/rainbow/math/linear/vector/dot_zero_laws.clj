(ns rainbow.math.linear.vector.dot-zero-laws
  "Zero laws for the native dot product and exact squared norm.

    vector/dot-zero-like-left
    vector/dot-zero-like-right
    norm/norm-squared-zero-like
    norm/is-norm-zero-like

  `vector/zero-like` preserves the input list shape while replacing every
  component by signed zero.  A native List induction proves its dot product is
  zero against arbitrary weights; commutativity supplies the other side.  The
  squared-norm and exact-zero-witness laws are immediate corollaries."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.vector.dot-subtract :as subtract]
            [rainbow.math.linear.vector.norm :as norm]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))
(defn- is-norm [values candidate]
  (app (function/const* 'norm/is-norm []) values candidate))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(def dot-zero-like-left-spec
  {:name 'vector/dot-zero-like-left :universes []
   :type
   (function/forall
    [['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot (zero-like 'values) 'weights) signed-zero))
   :value
   (function/lam
    [['values vector-type] ['weights vector-type]]
    (let [outer-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-weights vector-type]]
            (signed-equivalent
             (dot (zero-like 'current-values) 'current-weights)
             signed-zero)))
          outer-base
          (function/lam
           [['current-weights vector-type]]
           (app (function/const* 'signed/equivalent-reflexive [])
                signed-zero))
          outer-step
          (function/lam
           [['ignored-head signed] ['value-tail vector-type]
            ['tail-zero (app outer-motive 'value-tail)]]
           (let [current-values
                 (cons-vector 'ignored-head 'value-tail)
                 weight-motive
                 (function/lam
                  [['current-weights vector-type]]
                  (signed-equivalent
                   (dot (zero-like current-values) 'current-weights)
                   signed-zero))]
             (function/lam
              [['current-weights vector-type]]
              (list-rec
               weight-motive
               (app (function/const* 'signed/equivalent-reflexive [])
                    signed-zero)
               (function/lam
                [['weight-head signed] ['weight-tail vector-type]
                 ['ignored-weight (app weight-motive 'weight-tail)]]
                (let [zero-product
                      (signed-multiply signed-zero 'weight-head)
                      tail-dot (dot (zero-like 'value-tail) 'weight-tail)
                      start (signed-add zero-product tail-dot)
                      middle (signed-add signed-zero signed-zero)
                      split
                      (app
                       (function/const* 'signed/add-respects-equivalence [])
                       zero-product signed-zero
                       tail-dot signed-zero
                       (app (function/const* 'signed/multiply-zero-left [])
                            'weight-head)
                       (app 'tail-zero 'weight-tail))]
                  (transitive
                   start middle signed-zero
                   split
                   (app (function/const* 'signed/add-zero-right [])
                        signed-zero))))
               'current-weights))))]
      (app (list-rec outer-motive outer-base outer-step 'values)
           'weights)))})

(def dot-zero-like-right-spec
  {:name 'vector/dot-zero-like-right :universes []
   :type
   (function/forall
    [['weights vector-type] ['values vector-type]]
    (signed-equivalent
     (dot 'weights (zero-like 'values)) signed-zero))
   :value
   (function/lam
    [['weights vector-type] ['values vector-type]]
    (let [zeros (zero-like 'values)
          start (dot 'weights zeros)
          commuted (dot zeros 'weights)]
      (transitive
       start commuted signed-zero
       (app (function/const* 'vector/dot-commutative [])
            'weights zeros)
       (app (function/const* 'vector/dot-zero-like-left [])
            'values 'weights))))})

(def norm-squared-zero-like-spec
  {:name 'norm/norm-squared-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]]
    (signed-equivalent
     (norm-squared (zero-like 'values)) signed-zero))
   :value
   (function/lam
    [['values vector-type]]
    (app (function/const* 'vector/dot-zero-like-left [])
         'values (zero-like 'values)))})

(def is-norm-zero-like-spec
  {:name 'norm/is-norm-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]]
    (is-norm (zero-like 'values) signed-zero))
   :value
   (function/lam
    [['values vector-type]]
    (let [zero-square (signed-multiply signed-zero signed-zero)
          vector-square (norm-squared (zero-like 'values))]
      (transitive
       zero-square signed-zero vector-square
       (app (function/const* 'signed/multiply-zero-left []) signed-zero)
       (symmetric
        vector-square signed-zero
        (app (function/const* 'norm/norm-squared-zero-like [])
             'values)))))})

(def definition-specs [])
(def theorem-specs
  [dot-zero-like-left-spec
   dot-zero-like-right-spec
   norm-squared-zero-like-spec
   is-norm-zero-like-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.norm])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-spec-if-missing 'signed/multiply-zero-left :signed-distributive distributive/multiply-zero-left-spec) (support/extend-with :vector-dot-zero-laws theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.linear.vector.dot-zero-laws))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
