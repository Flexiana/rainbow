(ns rainbow.math.linear.vector.add-reorder
  "Four-term reordering and additive distribution for vector subtraction.

    (a + b) + (c + d)  ~  (a + c) + (b + d)
    (a + b) - (c + d)  ~  (a - c) + (b - d)

  Both statements remain valid for truncating vector addition because all sides
  stop at the same minimum input dimension.  Proofs compose existing checked
  vector algebra laws and add no recursion."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.linear.vector.subtract-negation :as subtract-negation]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def signed (function/const* 'signed/SignedRational []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- vector-add [left right]
  (app (function/const* 'vector/add []) left right))
(defn- vector-negate [values]
  (app (function/const* 'vector/negate []) values))
(defn- vector-subtract [left right]
  (app (function/const* 'vector/subtract []) left right))
(defn- vector-equivalent [left right]
  (app (function/const* 'vector/equivalent []) left right))
(defn- transitive [left middle right first second]
  (app (function/const* 'vector/equivalent-transitive [])
       left middle right first second))
(defn- symmetric [left right same]
  (app (function/const* 'vector/equivalent-symmetric [])
       left right same))
(defn- reflexive [values]
  (app (function/const* 'vector/equivalent-reflexive []) values))
(defn- add-respects [left left-prime right right-prime left-same right-same]
  (app (function/const* 'vector/add-respects-equivalence [])
       left left-prime right right-prime left-same right-same))

(def add-four-reorder-spec
  {:name 'vector/add-four-reorder :universes []
   :type
   (function/forall
    [['a vector-type] ['b vector-type]
     ['c vector-type] ['d vector-type]]
    (vector-equivalent
     (vector-add (vector-add 'a 'b) (vector-add 'c 'd))
     (vector-add (vector-add 'a 'c) (vector-add 'b 'd))))
   :value
   (function/lam
    [['a vector-type] ['b vector-type]
     ['c vector-type] ['d vector-type]]
    (let [bc (vector-add 'b 'c)
          cb (vector-add 'c 'b)
          cd (vector-add 'c 'd)
          bd (vector-add 'b 'd)
          start (vector-add (vector-add 'a 'b) cd)
          step-one (vector-add 'a (vector-add 'b cd))
          step-two (vector-add 'a (vector-add bc 'd))
          step-three (vector-add 'a (vector-add cb 'd))
          step-four (vector-add 'a (vector-add 'c bd))
          finish (vector-add (vector-add 'a 'c) bd)
          first
          (app (function/const* 'vector/add-associative []) 'a 'b cd)
          second-inner
          (symmetric
           (vector-add bc 'd) (vector-add 'b cd)
           (app (function/const* 'vector/add-associative []) 'b 'c 'd))
          second
          (add-respects
           'a 'a (vector-add 'b cd) (vector-add bc 'd)
           (reflexive 'a) second-inner)
          reorder-inner
          (add-respects
           bc cb 'd 'd
           (app (function/const* 'vector/add-commutative []) 'b 'c)
           (reflexive 'd))
          third
          (add-respects
           'a 'a (vector-add bc 'd) (vector-add cb 'd)
           (reflexive 'a) reorder-inner)
          fourth
          (add-respects
           'a 'a (vector-add cb 'd) (vector-add 'c bd)
           (reflexive 'a)
           (app (function/const* 'vector/add-associative []) 'c 'b 'd))
          fifth
          (symmetric
           finish step-four
           (app (function/const* 'vector/add-associative []) 'a 'c bd))]
      (transitive
       start step-four finish
       (transitive
        start step-three step-four
        (transitive
         start step-two step-three
         (transitive start step-one step-two first second)
         third)
        fourth)
       fifth)))})

(def subtract-additive-spec
  {:name 'vector/subtract-additive :universes []
   :type
   (function/forall
    [['a vector-type] ['b vector-type]
     ['c vector-type] ['d vector-type]]
    (vector-equivalent
     (vector-subtract (vector-add 'a 'b) (vector-add 'c 'd))
     (vector-add
      (vector-subtract 'a 'c)
      (vector-subtract 'b 'd))))
   :value
   (function/lam
    [['a vector-type] ['b vector-type]
     ['c vector-type] ['d vector-type]]
    (let [ab (vector-add 'a 'b)
          cd (vector-add 'c 'd)
          negated-c (vector-negate 'c)
          negated-d (vector-negate 'd)
          start (vector-subtract ab cd)
          distributed
          (vector-add ab (vector-add negated-c negated-d))
          finish
          (vector-add
           (vector-subtract 'a 'c)
           (vector-subtract 'b 'd))
          distribute-negation
          (add-respects
           ab ab
           (vector-negate cd)
           (vector-add negated-c negated-d)
           (reflexive ab)
           (app (function/const* 'vector/negate-additive []) 'c 'd))
          reorder
          (app (function/const* 'vector/add-four-reorder [])
               'a 'b negated-c negated-d)]
      (transitive
       start distributed finish distribute-negation reorder)))})

(def definition-specs [])
(def theorem-specs [add-four-reorder-spec subtract-additive-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      subtract-negation/extend-environment
      (support/extend-with :vector-add-reorder theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
