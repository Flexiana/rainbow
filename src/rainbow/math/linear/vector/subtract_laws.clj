(ns rainbow.math.linear.vector.subtract-laws
  "Congruence and mixed-variance order laws for native vector subtraction.

  Subtraction is addition of a negated vector.  Its first argument is monotone,
  its second argument is antitone, and it respects componentwise signed
  equivalence in both arguments.  These proofs compose existing checked vector
  laws and add no recursion, definitions, axioms, or trusted-base code."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.equivalence-laws :as signed-equivalence]
            [rainbow.math.linear.vector.add-order :as add-order]
            [rainbow.math.linear.vector.equivalence-laws :as equivalence-laws]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- vector-at-most [left right]
  (app (function/const* 'vector/at-most []) left right))

(def subtract-respects-equivalence-spec
  {:name 'vector/subtract-respects-equivalence :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (vector-equivalent
     (vector-subtract 'left 'right)
     (vector-subtract 'left-prime 'right-prime)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-same (vector-equivalent 'left 'left-prime)]
     ['right-same (vector-equivalent 'right 'right-prime)]]
    (app
     (function/const* 'vector/add-respects-equivalence [])
     'left 'left-prime
     (vector-negate 'right) (vector-negate 'right-prime)
     'left-same
     (app (function/const* 'vector/negate-respects-equivalence [])
          'right 'right-prime 'right-same)))})

(def subtract-left-monotone-spec
  {:name 'vector/subtract-left-monotone :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type] ['right vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]]
    (vector-at-most
     (vector-subtract 'left 'right)
     (vector-subtract 'left-prime 'right)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type] ['right vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]]
    (app (function/const* 'vector/add-right-monotone [])
         'left 'left-prime (vector-negate 'right) 'left-ordered))})

(def subtract-right-antitone-spec
  {:name 'vector/subtract-right-antitone :universes []
   :type
   (function/forall
    [['right vector-type] ['right-prime vector-type] ['left vector-type]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (vector-at-most
     (vector-subtract 'left 'right-prime)
     (vector-subtract 'left 'right)))
   :value
   (function/lam
    [['right vector-type] ['right-prime vector-type] ['left vector-type]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (app
     (function/const* 'vector/add-left-monotone [])
     (vector-negate 'right-prime) (vector-negate 'right) 'left
     (app (function/const* 'vector/negate-reverses-order [])
          'right 'right-prime 'right-ordered)))})

(def subtract-monotone-antitone-spec
  {:name 'vector/subtract-monotone-antitone :universes []
   :type
   (function/forall
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (vector-at-most
     (vector-subtract 'left 'right-prime)
     (vector-subtract 'left-prime 'right)))
   :value
   (function/lam
    [['left vector-type] ['left-prime vector-type]
     ['right vector-type] ['right-prime vector-type]
     ['left-ordered (vector-at-most 'left 'left-prime)]
     ['right-ordered (vector-at-most 'right 'right-prime)]]
    (app
     (function/const* 'vector/add-monotone [])
     'left 'left-prime
     (vector-negate 'right-prime) (vector-negate 'right)
     'left-ordered
     (app (function/const* 'vector/negate-reverses-order [])
          'right 'right-prime 'right-ordered)))})

(def definition-specs [])
(def theorem-specs
  [subtract-respects-equivalence-spec
   subtract-left-monotone-spec
   subtract-right-antitone-spec
   subtract-monotone-antitone-spec])

(defn- extend-signed-negate-equivalence-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment
                              'signed/negate-respects-equivalence)
    checked-environment
    (support/extend-with
     checked-environment :signed-equivalence-laws
     [signed-equivalence/negate-respects-equivalence-spec])))

(defn extend-environment [checked-environment]
  (-> checked-environment
      add-order/extend-environment
      extend-signed-negate-equivalence-if-missing
      equivalence-laws/extend-environment
      (support/extend-with :vector-subtract-laws theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
