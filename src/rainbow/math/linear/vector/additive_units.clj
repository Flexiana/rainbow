(ns rainbow.math.linear.vector.additive-units
  "Shape-preserving zero and additive-unit laws for native finite vectors.

  Since vector/add is a truncating zip, the empty vector cannot be a global
  additive identity.  vector/zero-like instead maps signed/zero over an input,
  preserving exactly its dimension.  It is a two-sided identity for that input,
  and adding either orientation of the input and its negation is equivalent to
  zero-like.  Native and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.limit-uniqueness :as signed-zero]
            [rainbow.math.rational.signed.unit-laws :as signed-units]
            [rainbow.math.linear.vector.add-order :as add-order]
            [rainbow.math.linear.vector.equivalence-transitivity :as transitivity]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))
(def signed-zero (function/const* 'signed/zero []))

(defn- app [f & args] (apply function/app f args))
(defn- nil-vector []
  (app (function/const* 'data/nil [type-level]) signed))
(defn- cons-vector [head tail]
  (app (function/const* 'data/cons [type-level]) signed head tail))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- list-map [mapping values]
  (app (function/const* 'list/map [type-level type-level])
       signed signed mapping values))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- zero-like [values]
  (app (function/const* 'vector/zero-like []) values))
(defn- conjunction [left right]
  (app (function/const* 'proposition/conjunction []) left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def trivial (function/const* 'proposition/trivial []))

(def zero-like-spec
  {:name 'vector/zero-like :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow vector-type vector-type)
   :value
   (function/lam
    [['values vector-type]]
    (list-map (function/lam [['ignored signed]] signed-zero) 'values))})

(def add-zero-like-right-spec
  {:name 'vector/add-zero-like-right :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-add 'values (zero-like 'values))
     'values))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-add 'current (zero-like 'current))
            'current))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-identity (app motive 'tail)]]
           (conjoin
            (signed-equivalent (signed-add 'head signed-zero) 'head)
            (vector-equivalent
             (vector-add 'tail (zero-like 'tail))
             'tail)
            (app (function/const* 'signed/add-zero-right []) 'head)
            'tail-identity))]
      (list-rec motive trivial step 'values)))})

(def add-zero-like-left-spec
  {:name 'vector/add-zero-like-left :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-add (zero-like 'values) 'values)
     'values))
   :value
   (function/lam
    [['values vector-type]]
    (app
     (function/const* 'vector/equivalent-transitive [])
     (vector-add (zero-like 'values) 'values)
     (vector-add 'values (zero-like 'values))
     'values
     (app (function/const* 'vector/add-commutative [])
          (zero-like 'values) 'values)
     (app (function/const* 'vector/add-zero-like-right []) 'values)))})

(def subtract-self-equivalent-zero-like-spec
  {:name 'vector/subtract-self-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-subtract 'values 'values)
     (zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (vector-equivalent
            (vector-subtract 'current 'current)
            (zero-like 'current)))
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-cancels (app motive 'tail)]]
           (conjoin
            (signed-equivalent
             (signed-subtract 'head 'head)
             signed-zero)
            (vector-equivalent
             (vector-subtract 'tail 'tail)
             (zero-like 'tail))
            (app
             (function/const* 'signed/subtract-self-equivalent-zero [])
             'head)
            'tail-cancels))]
      (list-rec motive trivial step 'values)))})

(def add-negate-right-equivalent-zero-like-spec
  {:name 'vector/add-negate-right-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-add 'values (vector-negate 'values))
     (zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (app
     (function/const* 'vector/subtract-self-equivalent-zero-like [])
     'values))})

(def add-negate-left-equivalent-zero-like-spec
  {:name 'vector/add-negate-left-equivalent-zero-like :universes []
   :type
   (function/forall
    [['values vector-type]]
    (vector-equivalent
     (vector-add (vector-negate 'values) 'values)
     (zero-like 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (app
     (function/const* 'vector/equivalent-transitive [])
     (vector-add (vector-negate 'values) 'values)
     (vector-add 'values (vector-negate 'values))
     (zero-like 'values)
     (app (function/const* 'vector/add-commutative [])
          (vector-negate 'values) 'values)
     (app
      (function/const* 'vector/add-negate-right-equivalent-zero-like [])
      'values)))})

(def definition-specs [zero-like-spec])
(def theorem-specs
  [add-zero-like-right-spec
   add-zero-like-left-spec
   subtract-self-equivalent-zero-like-spec
   add-negate-right-equivalent-zero-like-spec
   add-negate-left-equivalent-zero-like-spec])

(defn- extend-spec-if-missing
  [checked-environment alias milestone spec]
  (if (environment/resolve-id checked-environment alias)
    checked-environment
    (support/extend-with checked-environment milestone [spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      signed-units/extend-environment
      (extend-spec-if-missing
       'signed/add-zero-right :signed-limit-uniqueness
       signed-zero/signed-add-zero-right-spec)
      add-order/extend-environment
      (extend-spec-if-missing
       'vector/equivalent-transitive :vector-equivalence-transitivity
       transitivity/equivalent-transitive-spec)
      (support/extend-with :vector-additive-units
                           (into definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
