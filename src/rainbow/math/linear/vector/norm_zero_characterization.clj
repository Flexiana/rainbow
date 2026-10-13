(ns rainbow.math.linear.vector.norm-zero-characterization
  "The proved forward zero-characterization for native exact norms.

    norm/norm-squared-zero-of-equivalent-zero-like
    norm/is-norm-zero-of-equivalent-zero-like

  A vector componentwise equivalent to its shape-preserving zero vector has
  squared norm equivalent to signed zero, and signed zero is an exact norm
  witness.  These are the forward directions; the converses are proved in
  rainbow.math.linear.vector.norm-zero-reflection."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.multiply-ring :as signed-ring]
            [rainbow.math.linear.vector.dot-zero-laws :as zero-laws]
            [rainbow.math.linear.vector.norm-congruence :as congruence]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
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

(def norm-squared-zero-of-equivalent-zero-like-spec
  {:name 'norm/norm-squared-zero-of-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]
     ['zero-equivalent
      (vector-equivalent 'values (zero-like 'values))]]
    (signed-equivalent (norm-squared 'values) signed-zero))
   :value
   (function/lam
    [['values vector-type]
     ['zero-equivalent
      (vector-equivalent 'values (zero-like 'values))]]
    (transitive
     (norm-squared 'values)
     (norm-squared (zero-like 'values))
     signed-zero
     (app
      (function/const* 'norm/norm-squared-respects-equivalence [])
      'values (zero-like 'values) 'zero-equivalent)
     (app (function/const* 'norm/norm-squared-zero-like [])
          'values)))})

(def is-norm-zero-of-equivalent-zero-like-spec
  {:name 'norm/is-norm-zero-of-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]
     ['zero-equivalent
      (vector-equivalent 'values (zero-like 'values))]]
    (is-norm 'values signed-zero))
   :value
   (function/lam
    [['values vector-type]
     ['zero-equivalent
      (vector-equivalent 'values (zero-like 'values))]]
    (let [zero-square (signed-multiply signed-zero signed-zero)
          vector-square (norm-squared 'values)]
      (transitive
       zero-square signed-zero vector-square
       (app (function/const* 'signed/multiply-zero-left []) signed-zero)
       (symmetric
        vector-square signed-zero
        (app
         (function/const*
          'norm/norm-squared-zero-of-equivalent-zero-like [])
         'values 'zero-equivalent)))))})

(def definition-specs [])
(def theorem-specs
  [norm-squared-zero-of-equivalent-zero-like-spec
   is-norm-zero-of-equivalent-zero-like-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn- extend-specs-if-missing
  [checked-environment milestone specs]
  (reduce
   (fn [current spec]
     (extend-spec-if-missing current (:name spec) milestone spec))
   checked-environment
   specs))

(defn extend-environment [checked-environment]
  (-> checked-environment
      zero-laws/extend-environment
      (extend-specs-if-missing
       :signed-multiply-ring signed-ring/theorem-specs)
      (extend-spec-if-missing
       'norm/norm-squared-respects-equivalence
       :vector-norm-congruence
       congruence/norm-squared-respects-equivalence-spec)
      (support/extend-with :vector-norm-zero-characterization theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
