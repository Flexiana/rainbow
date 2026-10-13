(ns rainbow.math.linear.vector.norm-nonnegative
  "Constructive nonnegativity of signed squares and native squared norms.

    signed/add-nonnegative
    signed/square-nonnegative
    norm/norm-squared-nonnegative

  A signed square is nonnegative by case-splitting the computable comparison
  with zero: either both factors are nonpositive or both are nonnegative.
  Signed addition preserves componentwise nonnegativity by nnrat add
  monotonicity.  Squared-norm nonnegativity is then one List induction over the
  sum of component squares."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as function]
            [rainbow.algorithms.proofs.inner-product :as inner]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.linear.vector.norm :as norm]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def signed (function/const* 'signed/SignedRational []))
(def signed-zero (function/const* 'signed/zero []))
(def vector-type
  (function/app (function/const* 'data/List [type-level]) signed))

(defn- app [f & args] (apply function/app f args))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- list-rec [motive base step values]
  (app (function/const* 'data/List.rec [type-level zero-level])
       signed motive base step values))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- signed-add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- signed-multiply [left right]
  (app (function/const* 'signed/multiply []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- nonnegative [value]
  (app (function/const* 'signed/nonnegative []) value))
(defn- nonpositive [value]
  (app (function/const* 'signed/nonpositive []) value))
(defn- decide-at-most [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- norm-squared [values]
  (app (function/const* 'norm/norm-squared []) values))

(def add-nonnegative-spec
  {:name 'signed/add-nonnegative :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]]
    (nonnegative (signed-add 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['left-nonnegative (nonnegative 'left)]
     ['right-nonnegative (nonnegative 'right)]]
    (app (function/const* 'nnrat/add-monotone [])
         (negative 'left) (positive 'left)
         (negative 'right) (positive 'right)
         'left-nonnegative 'right-nonnegative))})

(def square-nonnegative-spec
  {:name 'signed/square-nonnegative :universes []
   :type
   (function/forall
    [['value signed]]
    (nonnegative (signed-multiply 'value 'value)))
   :value
   (function/lam
    [['value signed]]
    (let [decision (decide-at-most 'value signed-zero)
          square (signed-multiply 'value 'value)
          motive
          (function/lam
           [['choice bool]]
           (function/arrow
            (eq-bool decision 'choice)
            (nonnegative square)))
          at-false
          (function/lam
           [['decided-false (eq-bool decision false-value)]]
           (let [zero-at-most-value
                 (app
                  (function/const*
                   'signed/decide-at-most-false-reverse [])
                  'value signed-zero 'decided-false)
                 value-nonnegative
                 (app
                  (function/const* 'signed/nonnegative-of-zero-at-most [])
                  'value zero-at-most-value)]
             (app (function/const* 'signed/multiply-nonnegative [])
                  'value 'value value-nonnegative value-nonnegative)))
          at-true
          (function/lam
           [['decided-true (eq-bool decision true-value)]]
           (let [value-at-most-zero
                 (app
                  (function/const* 'signed/decide-at-most-true-sound [])
                  'value signed-zero 'decided-true)
                 value-nonpositive
                 (app
                  (function/const* 'signed/nonpositive-of-at-most-zero [])
                  'value value-at-most-zero)]
             (app (function/const* 'signed/multiply-nonpositive [])
                  'value 'value value-nonpositive value-nonpositive)))]
      (app
       (app (function/const* 'data/Bool.rec [zero-level])
            motive at-false at-true decision)
       (app (function/const* 'equality/reflexive [type-level])
            bool decision))))})

(def norm-squared-nonnegative-spec
  {:name 'norm/norm-squared-nonnegative :universes []
   :type
   (function/forall
    [['values vector-type]]
    (nonnegative (norm-squared 'values)))
   :value
   (function/lam
    [['values vector-type]]
    (let [motive
          (function/lam
           [['current vector-type]]
           (nonnegative (norm-squared 'current)))
          base
          (app (function/const* 'nnrat/at-most-reflexive []) nnrat-zero)
          step
          (function/lam
           [['head signed] ['tail vector-type]
            ['tail-nonnegative (app motive 'tail)]]
           (let [square (signed-multiply 'head 'head)]
             (app (function/const* 'signed/add-nonnegative [])
                  square (norm-squared 'tail)
                  (app (function/const* 'signed/square-nonnegative [])
                       'head)
                  'tail-nonnegative)))]
      (list-rec motive base step 'values)))})

(def definition-specs [])
(def theorem-specs
  [add-nonnegative-spec
   square-nonnegative-spec
   norm-squared-nonnegative-spec])

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
      multiply-order/extend-environment
      (extend-specs-if-missing
       :signed-decide-order
       (concat decide/definition-specs decide/theorem-specs))
      (extend-specs-if-missing
       :nnrat-add-monotone add-monotone/theorem-specs)
      inner/extend-environment
      norm/extend-environment
      (support/extend-with :vector-norm-nonnegative theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
