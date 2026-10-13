(ns rainbow.math.rational.signed.minmax-algebra
  "Algebraic and monotonicity laws for signed extrema.

  Signed rationals are quotient-like Grothendieck pairs, so algebraic laws are
  stated with signed/equivalent rather than structural equality.  The lattice
  bounds from rainbow.math.rational.signed.minmax and order transitivity prove:

    min/max commutativity, idempotence, monotonicity, and associativity.

  Each equivalence is obtained by antisymmetry after proving the two order
  directions.  No arithmetic representation is unfolded here: this is exactly
  the reusable structural layer that robust aggregation, dynamic programming,
  and finite extrema can depend on.  Native and axiom-free on D63."
  (:refer-clojure :exclude [min max])
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]
            [rainbow.math.rational.signed.minmax :as minmax]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- minimum [left right]
  (app (function/const* 'signed/min []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))
(defn- reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- transitive [left middle right left-middle middle-right]
  (app (function/const* 'signed/at-most-transitive [])
       left middle right left-middle middle-right))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'signed/at-most-antisymmetric [])
       left right left-right right-left))
(defn- min-left [left right]
  (app (function/const* 'signed/min-lower-left []) left right))
(defn- min-right [left right]
  (app (function/const* 'signed/min-lower-right []) left right))
(defn- max-left [left right]
  (app (function/const* 'signed/max-upper-left []) left right))
(defn- max-right [left right]
  (app (function/const* 'signed/max-upper-right []) left right))
(defn- below-min [lower left right lower-left lower-right]
  (app (function/const* 'signed/at-most-min [])
       lower left right lower-left lower-right))
(defn- max-below [left right upper left-upper right-upper]
  (app (function/const* 'signed/at-most-max [])
       left right upper left-upper right-upper))

(def min-commutative-spec
  {:name 'signed/min-commutative :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (equivalent (minimum 'left 'right) (minimum 'right 'left)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [lr (minimum 'left 'right)
          rl (minimum 'right 'left)]
      (antisymmetric
       lr rl
       (below-min lr 'right 'left
                  (min-right 'left 'right) (min-left 'left 'right))
       (below-min rl 'left 'right
                  (min-right 'right 'left) (min-left 'right 'left)))))})

(def max-commutative-spec
  {:name 'signed/max-commutative :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (equivalent (maximum 'left 'right) (maximum 'right 'left)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (let [lr (maximum 'left 'right)
          rl (maximum 'right 'left)]
      (antisymmetric
       lr rl
       (max-below 'left 'right rl
                  (max-right 'right 'left) (max-left 'right 'left))
       (max-below 'right 'left lr
                  (max-right 'left 'right) (max-left 'left 'right)))))})

(def min-idempotent-spec
  {:name 'signed/min-idempotent :universes []
   :type
   (function/forall
    [['value signed]]
    (equivalent (minimum 'value 'value) 'value))
   :value
   (function/lam
    [['value signed]]
    (antisymmetric
     (minimum 'value 'value) 'value
     (min-left 'value 'value)
     (below-min 'value 'value 'value
                (reflexive 'value) (reflexive 'value))))})

(def max-idempotent-spec
  {:name 'signed/max-idempotent :universes []
   :type
   (function/forall
    [['value signed]]
    (equivalent (maximum 'value 'value) 'value))
   :value
   (function/lam
    [['value signed]]
    (antisymmetric
     (maximum 'value 'value) 'value
     (max-below 'value 'value 'value
                (reflexive 'value) (reflexive 'value))
     (max-left 'value 'value)))})

(def min-monotone-spec
  {:name 'signed/min-monotone :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['left-order (at-most 'left 'left-prime)]
     ['right-order (at-most 'right 'right-prime)]]
    (at-most (minimum 'left 'right)
             (minimum 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['left-order (at-most 'left 'left-prime)]
     ['right-order (at-most 'right 'right-prime)]]
    (let [lower (minimum 'left 'right)]
      (below-min
       lower 'left-prime 'right-prime
       (transitive lower 'left 'left-prime
                   (min-left 'left 'right) 'left-order)
       (transitive lower 'right 'right-prime
                   (min-right 'left 'right) 'right-order))))})

(def max-monotone-spec
  {:name 'signed/max-monotone :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['left-order (at-most 'left 'left-prime)]
     ['right-order (at-most 'right 'right-prime)]]
    (at-most (maximum 'left 'right)
             (maximum 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-prime signed] ['right-prime signed]
     ['left-order (at-most 'left 'left-prime)]
     ['right-order (at-most 'right 'right-prime)]]
    (let [upper (maximum 'left-prime 'right-prime)]
      (max-below
       'left 'right upper
       (transitive 'left 'left-prime upper
                   'left-order (max-left 'left-prime 'right-prime))
       (transitive 'right 'right-prime upper
                   'right-order (max-right 'left-prime 'right-prime)))))})

(def min-associative-spec
  {:name 'signed/min-associative :universes []
   :type
   (function/forall
    [['a signed] ['b signed] ['c signed]]
    (equivalent (minimum (minimum 'a 'b) 'c)
                (minimum 'a (minimum 'b 'c))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]]
    (let [ab (minimum 'a 'b)
          bc (minimum 'b 'c)
          left (minimum ab 'c)
          right (minimum 'a bc)
          left<=ab (min-left ab 'c)
          left<=a (transitive left ab 'a left<=ab (min-left 'a 'b))
          left<=b (transitive left ab 'b left<=ab (min-right 'a 'b))
          left<=c (min-right ab 'c)
          left<=bc (below-min left 'b 'c left<=b left<=c)
          left<=right (below-min left 'a bc left<=a left<=bc)
          right<=a (min-left 'a bc)
          right<=bc (min-right 'a bc)
          right<=b (transitive right bc 'b right<=bc (min-left 'b 'c))
          right<=c (transitive right bc 'c right<=bc (min-right 'b 'c))
          right<=ab (below-min right 'a 'b right<=a right<=b)
          right<=left (below-min right ab 'c right<=ab right<=c)]
      (antisymmetric left right left<=right right<=left)))})

(def max-associative-spec
  {:name 'signed/max-associative :universes []
   :type
   (function/forall
    [['a signed] ['b signed] ['c signed]]
    (equivalent (maximum (maximum 'a 'b) 'c)
                (maximum 'a (maximum 'b 'c))))
   :value
   (function/lam
    [['a signed] ['b signed] ['c signed]]
    (let [ab (maximum 'a 'b)
          bc (maximum 'b 'c)
          left (maximum ab 'c)
          right (maximum 'a bc)
          a<=ab (max-left 'a 'b)
          b<=ab (max-right 'a 'b)
          ab<=left (max-left ab 'c)
          a<=left (transitive 'a ab left a<=ab ab<=left)
          b<=left (transitive 'b ab left b<=ab ab<=left)
          c<=left (max-right ab 'c)
          bc<=left (max-below 'b 'c left b<=left c<=left)
          right<=left (max-below 'a bc left a<=left bc<=left)
          b<=bc (max-left 'b 'c)
          c<=bc (max-right 'b 'c)
          bc<=right (max-right 'a bc)
          b<=right (transitive 'b bc right b<=bc bc<=right)
          c<=right (transitive 'c bc right c<=bc bc<=right)
          a<=right (max-left 'a bc)
          ab<=right (max-below 'a 'b right a<=right b<=right)
          left<=right (max-below ab 'c right ab<=right c<=right)]
      (antisymmetric left right left<=right right<=left)))})

(def definition-specs [])
(def theorem-specs
  [min-commutative-spec max-commutative-spec
   min-idempotent-spec max-idempotent-spec
   min-monotone-spec max-monotone-spec
   min-associative-spec max-associative-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      uniqueness/extend-environment
      minmax/extend-environment
      (support/extend-with :signed-minmax-algebra theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
