(ns rainbow.math.rational.signed.square-zero
  "A signed rational whose square is zero is itself zero.

    signed/square-zero-reflects : x*x ~ 0 -> x ~ 0

  For x=(p,n), signed multiplication exposes the two components

      positive(x*x) = p*p + n*n
      negative(x*x) = p*n + n*p.

  Equivalence of x*x with signed zero is therefore the quadratic equality
  proved by nnrat/quadratic-equality-reflects, modulo the zero padding in the
  Grothendieck relation.  Native and axiom-free."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.quadratic-zero :as quadratic]
            [rainbow.math.rational.signed.multiply :as multiply]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rat-equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- smul [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- rat-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- rat-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- add-zero-right [value]
  (app (function/const* 'nnrat/add-zero-right []) value))
(defn- add-zero-left [value]
  (app (function/const* 'nnrat/add-zero-left []) value))

(def square-zero-reflects-spec
  {:name 'signed/square-zero-reflects :universes []
   :type
   (function/forall
    [['value signed]
     ['zero-square (signed-equivalent (smul 'value 'value) signed-zero)]]
    (signed-equivalent 'value signed-zero))
   :value
   (function/lam
    [['value signed]
     ['zero-square (signed-equivalent (smul 'value 'value) signed-zero)]]
    (let [p (positive 'value)
          n (negative 'value)
          square-positive (radd (rmul p p) (rmul n n))
          square-negative (radd (rmul p n) (rmul n p))
          padded-positive (radd square-positive nnrat-zero)
          padded-negative (radd nnrat-zero square-negative)
          balanced
          (rat-transitive
           square-positive padded-positive square-negative
           (rat-symmetric padded-positive square-positive
                          (add-zero-right square-positive))
           (rat-transitive
            padded-positive padded-negative square-negative
            'zero-square
            (add-zero-left square-negative)))
          components-same
          (app (function/const* 'nnrat/quadratic-equality-reflects [])
               p n balanced)
          value-positive-padded (radd p nnrat-zero)
          value-negative-padded (radd nnrat-zero n)]
      (rat-transitive
       value-positive-padded p value-negative-padded
       (add-zero-right p)
       (rat-transitive
        p n value-negative-padded
        components-same
        (rat-symmetric value-negative-padded n (add-zero-left n))))))})

(def definition-specs [])
(def theorem-specs [square-zero-reflects-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      quadratic/extend-environment
      (extend-spec-if-missing
       'signed/multiply :signed-multiply multiply/multiply-spec)
      (extend-spec-if-missing
       'nnrat/add-zero-left :nnrat-identities
       identities/add-zero-left-spec)
      (support/extend-with :signed-square-zero theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
