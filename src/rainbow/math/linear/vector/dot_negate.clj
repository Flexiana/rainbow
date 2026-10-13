(ns rainbow.math.linear.vector.dot-negate
  "Negation laws for signed multiplication and the native vector dot product.

    signed/negate-zero
    signed/multiply-negate-left
    signed/multiply-negate-right
    vector/dot-negate-left
    vector/dot-negate-right

  The scalar product laws are unfolded Grothendieck-pair ring identities.  The
  left dot law is a native List induction, while the right law follows from dot
  commutativity and quotient-safe negation congruence.  No shape hypothesis is
  needed because componentwise negation preserves every list position."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.equivalence-laws :as signed-equivalence]
            [rainbow.math.rational.signed.negate-additive :as signed-additive]
            [rainbow.math.linear.vector.dot-bilinear :as bilinear]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- dot [left right]
  (app (function/const* 'vector/dot []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))

(defn- product-positive [pl nl pr nr]
  (ring/radd (ring/rmul pl pr) (ring/rmul nl nr)))
(defn- product-negative [pl nl pr nr]
  (ring/radd (ring/rmul pl nr) (ring/rmul nl pr)))

(def negate-zero-spec
  {:name 'signed/negate-zero :universes []
   :type
   (signed-equivalent (signed-negate signed-zero) signed-zero)
   :value
   (app (function/const* 'signed/equivalent-reflexive []) signed-zero)})

(def multiply-negate-left-spec
  {:name 'signed/multiply-negate-left :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (signed-equivalent
     (signed-multiply (signed-negate 'left) 'right)
     (signed-negate (signed-multiply 'left 'right))))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [pl (positive 'left)
          nl (negative 'left)
          pr (positive 'right)
          nr (negative 'right)
          left-positive (product-positive nl pl pr nr)
          left-negative (product-negative nl pl pr nr)
          right-positive (product-negative pl nl pr nr)
          right-negative (product-positive pl nl pr nr)]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def multiply-negate-right-spec
  {:name 'signed/multiply-negate-right :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (signed-equivalent
     (signed-multiply 'left (signed-negate 'right))
     (signed-negate (signed-multiply 'left 'right))))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [pl (positive 'left)
          nl (negative 'left)
          pr (positive 'right)
          nr (negative 'right)
          left-positive (product-positive pl nl nr pr)
          left-negative (product-negative pl nl nr pr)
          right-positive (product-negative pl nl pr nr)
          right-negative (product-positive pl nl pr nr)]
      (ring/equiv
       (ring/radd left-positive right-negative)
       (ring/radd right-positive left-negative))))})

(def dot-negate-left-spec
  {:name 'vector/dot-negate-left :universes []
   :type
   (function/forall
    [['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot (vector-negate 'values) 'weights)
     (signed-negate (dot 'values 'weights))))
   :value
   (function/lam
    [['values vector-type] ['weights vector-type]]
    (let [zero-backward
          (symmetric
           (signed-negate signed-zero) signed-zero
           (function/const* 'signed/negate-zero []))
          outer-motive
          (function/lam
           [['current-values vector-type]]
           (function/forall
            [['current-weights vector-type]]
            (signed-equivalent
             (dot (vector-negate 'current-values) 'current-weights)
             (signed-negate
              (dot 'current-values 'current-weights)))))
          outer-base
          (function/lam
           [['current-weights vector-type]]
           zero-backward)
          outer-step
          (function/lam
           [['value-head signed] ['value-tail vector-type]
            ['tail-negates (app outer-motive 'value-tail)]]
           (let [current-values
                 (app (function/const* 'data/cons [type-level])
                      signed 'value-head 'value-tail)
                 weight-motive
                 (function/lam
                  [['current-weights vector-type]]
                  (signed-equivalent
                   (dot (vector-negate current-values) 'current-weights)
                   (signed-negate
                    (dot current-values 'current-weights))))]
             (function/lam
              [['current-weights vector-type]]
              (list-rec
               weight-motive
               zero-backward
               (function/lam
                [['weight-head signed] ['weight-tail vector-type]
                 ['ignored (app weight-motive 'weight-tail)]]
                (let [product
                      (signed-multiply 'value-head 'weight-head)
                      negated-product
                      (signed-multiply
                       (signed-negate 'value-head) 'weight-head)
                      tail-dot (dot 'value-tail 'weight-tail)
                      negated-tail-dot
                      (dot (vector-negate 'value-tail) 'weight-tail)
                      start (signed-add negated-product negated-tail-dot)
                      middle
                      (signed-add
                       (signed-negate product)
                       (signed-negate tail-dot))
                      finish
                      (signed-negate (signed-add product tail-dot))
                      split
                      (app
                       (function/const* 'signed/add-respects-equivalence [])
                       negated-product (signed-negate product)
                       negated-tail-dot (signed-negate tail-dot)
                       (app (function/const* 'signed/multiply-negate-left [])
                            'value-head 'weight-head)
                       (app 'tail-negates 'weight-tail))
                      combine
                      (symmetric
                       finish middle
                       (app (function/const* 'signed/negate-additive [])
                            product tail-dot))]
                  (transitive start middle finish split combine)))
               'current-weights))))]
      (app (list-rec outer-motive outer-base outer-step 'values)
           'weights)))})

(def dot-negate-right-spec
  {:name 'vector/dot-negate-right :universes []
   :type
   (function/forall
    [['values vector-type] ['weights vector-type]]
    (signed-equivalent
     (dot 'values (vector-negate 'weights))
     (signed-negate (dot 'values 'weights))))
   :value
   (function/lam
    [['values vector-type] ['weights vector-type]]
    (let [negated-weights (vector-negate 'weights)
          start (dot 'values negated-weights)
          commuted (dot negated-weights 'values)
          negated-commuted (signed-negate (dot 'weights 'values))
          finish (signed-negate (dot 'values 'weights))]
      (transitive
       start negated-commuted finish
       (transitive
        start commuted negated-commuted
        (app (function/const* 'vector/dot-commutative [])
             'values negated-weights)
        (app (function/const* 'vector/dot-negate-left [])
             'weights 'values))
       (app (function/const* 'signed/negate-respects-equivalence [])
            (dot 'weights 'values) (dot 'values 'weights)
            (app (function/const* 'vector/dot-commutative [])
                 'weights 'values)))))})

(def definition-specs [])
(def theorem-specs
  [negate-zero-spec
   multiply-negate-left-spec
   multiply-negate-right-spec
   dot-negate-left-spec
   dot-negate-right-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      bilinear/extend-environment
      ring/extend-environment
      (extend-spec-if-missing
       'signed/negate-additive :signed-negate-additive
       signed-additive/negate-additive-spec)
      (extend-spec-if-missing
       'signed/negate-respects-equivalence :signed-equivalence-laws
       signed-equivalence/negate-respects-equivalence-spec)
      (support/extend-with :vector-dot-negate theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
