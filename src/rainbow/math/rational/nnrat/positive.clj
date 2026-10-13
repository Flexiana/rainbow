(ns rainbow.math.rational.nnrat.positive
  "Constructive strict positivity for exact nonnegative rationals.

  A nonnegative rational is positive exactly when its numerator is a positive
  natural.  This representation-facing definition is executable and avoids
  quotient reasoning.  Positivity is invariant under exact-rational
  equivalence, and addition, multiplication, division, and minimum preserve
  it.  These are the algebraic prerequisites for full-support Hastings
  reachability.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness :as bellman]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.metric-separation :as separation]
            [rainbow.math.nat.semiring :as semiring]
            [rainbow.math.rational.nnrat.add-monotone :as add-monotone]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.division :as division]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- numerator-of [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- denominator-predecessor [value]
  (app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- denominator-of [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- successor [value]
  (app (function/const* 'data/succ []) value))
(defn- nat-add [left right]
  (app (function/const* 'algebra/nat-add []) left right))
(defn- nat-multiply [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- multiply [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- nnrat-add [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- below [left right]
  (app (function/const* 'nat/strict-below []) left right))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- reciprocal [value]
  (app (function/const* 'nnrat/reciprocal []) value))
(defn- divide [left right]
  (app (function/const* 'nnrat/divide []) left right))
(defn- decide-at-most [left right]
  (app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- selected-at [when-false when-true choice]
  (app (function/const* 'data/Bool.rec [type-level])
       (function/lam [['ignored bool]] nnrat)
       when-false when-true choice))
(defn- minimum [left right]
  (app (function/const* 'minmax/min []) left right))
(defn- bool-equality [left right]
  (function/equality type-level bool left right))
(defn- nat-equality [left right]
  (function/equality type-level nat left right))
(defn- nat-reflexive [value]
  (app (function/const* 'equality/reflexive [type-level])
       nat value))
(defn- nat-symmetric [left right same]
  (app (function/const* 'equality/symmetric [type-level])
       nat left right same))
(defn- nat-transitive [left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       nat left middle right first second))
(defn- nat-congruent [mapping left right same]
  (app (function/const* 'equality/congruent-function
                        [type-level type-level])
       nat nat mapping left right same))

(def positive-spec
  {:name 'nnrat/positive
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nnrat 'Prop)
   :value
   (function/lam
    [['value nnrat]]
    (below nat-zero (numerator-of 'value)))})

(def one-positive-spec
  {:name 'nnrat/one-positive
   :universes []
   :type (positive nnrat-one)
   :value
   (app
    (function/const* 'proposition/witness [type-level])
    nat
    (function/lam
     [['extra nat]]
     (nat-equality
      (nat-add (successor nat-zero) 'extra)
      (successor nat-zero)))
    nat-zero
    (nat-reflexive (successor nat-zero)))})

(def multiply-positive-spec
  {:name 'nnrat/multiply-positive
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]
     ['right-positive (positive 'right)]]
    (positive (multiply 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]
     ['right-positive (positive 'right)]]
    (app
     (function/const* 'nat/multiply-right-strict-monotone-positive [])
     (numerator-of 'right) nat-zero (numerator-of 'left)
     'left-positive 'right-positive))})

(def positive-respects-equivalence-spec
  {:name 'nnrat/positive-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['same (equivalent 'left 'right)]
     ['left-positive (positive 'left)]]
    (positive 'right))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['same (equivalent 'left 'right)]
     ['left-positive (positive 'left)]]
    (let [left-numerator (numerator-of 'left)
          right-numerator (numerator-of 'right)
          left-denominator (denominator-of 'left)
          right-denominator (denominator-of 'right)
          right-denominator-predecessor (denominator-predecessor 'right)]
      (app
       (function/const* 'nat/positive-of-nonzero [])
       right-numerator
       (function/lam
        [['right-is-zero (nat-equality right-numerator nat-zero)]]
        (let [right-product-is-zero
              (nat-congruent
               (function/lam
                [['value nat]] (nat-multiply 'value left-denominator))
               right-numerator nat-zero 'right-is-zero)
              left-product-is-zero
              (nat-transitive
               (nat-multiply left-numerator right-denominator)
               (nat-multiply right-numerator left-denominator)
               (nat-multiply nat-zero left-denominator)
               'same right-product-is-zero)
              left-is-zero
              (app
               (function/const* 'nat/multiply-successor-right-cancel [])
               left-numerator nat-zero right-denominator-predecessor
               left-product-is-zero)
              left-nonzero
              (app
               (function/const* 'nat/nonzero-of-positive [])
               left-numerator 'left-positive)]
          (app left-nonzero left-is-zero))))))})

(def nat-add-positive-left-spec
  {:name 'nat/add-positive-left
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['left-positive (below nat-zero 'left)]]
    (below nat-zero (nat-add 'left 'right)))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['left-positive (below nat-zero 'left)]]
    (app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['gap nat]]
      (nat-equality (nat-add (successor nat-zero) 'gap) 'left))
     (below nat-zero (nat-add 'left 'right))
     'left-positive
     (function/lam
      [['gap nat]
       ['same
        (nat-equality (nat-add (successor nat-zero) 'gap) 'left)]]
      (let [start
            (nat-add (successor nat-zero) (nat-add 'gap 'right))
            middle
            (nat-add (nat-add (successor nat-zero) 'gap) 'right)
            finish (nat-add 'left 'right)]
        (app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam
          [['extra nat]]
          (nat-equality (nat-add (successor nat-zero) 'extra) finish))
         (nat-add 'gap 'right)
         (nat-transitive
          start middle finish
          (nat-symmetric
           middle start
           (app (function/const* 'nat/add-associative [])
                (successor nat-zero) 'gap 'right))
          (nat-congruent
           (function/lam [['value nat]] (nat-add 'value 'right))
           (nat-add (successor nat-zero) 'gap) 'left 'same)))))))})

(def denominator-positive-spec
  {:name 'nnrat/denominator-positive
   :universes []
   :type
   (function/forall
    [['value nnrat]]
    (below nat-zero (denominator-of 'value)))
   :value
   (function/lam
    [['value nnrat]]
    (let [previous (denominator-predecessor 'value)
          positive-denominator (successor previous)]
      (app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam
        [['extra nat]]
        (nat-equality (nat-add (successor nat-zero) 'extra)
                      positive-denominator))
       previous
       (nat-reflexive positive-denominator))))})

(def add-positive-left-spec
  {:name 'nnrat/add-positive-left
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]]
    (positive (nnrat-add 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]]
    (let [left-product
          (nat-multiply (numerator-of 'left) (denominator-of 'right))
          right-product
          (nat-multiply (numerator-of 'right) (denominator-of 'left))
          left-product-positive
          (app
           (function/const* 'nat/multiply-right-strict-monotone-positive [])
           (denominator-of 'right) nat-zero (numerator-of 'left)
           'left-positive
           (app (function/const* 'nnrat/denominator-positive []) 'right))]
      (app
       (function/const* 'nat/add-positive-left [])
       left-product right-product left-product-positive)))})

(def add-positive-right-spec
  {:name 'nnrat/add-positive-right
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['right-positive (positive 'right)]]
    (positive (nnrat-add 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['right-positive (positive 'right)]]
    (let [right-first (nnrat-add 'right 'left)
          left-first (nnrat-add 'left 'right)
          right-first-positive
          (app
           (function/const* 'nnrat/add-positive-left [])
           'right 'left 'right-positive)
          swapped
          (app
           (function/const* 'nnrat/add-commutative [])
           'right 'left)]
      (app
       (function/const* 'nnrat/positive-respects-equivalence [])
       right-first left-first swapped right-first-positive)))})

(def min-positive-spec
  (let [decision (decide-at-most 'left 'right)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (bool-equality decision 'choice)
          (positive (selected-at 'right 'left 'choice))))]
    {:name 'nnrat/min-positive
     :universes []
     :type
     (function/forall
      [['left nnrat] ['right nnrat]
       ['left-positive (positive 'left)]
       ['right-positive (positive 'right)]]
      (positive (minimum 'left 'right)))
     :value
     (function/lam
      [['left nnrat] ['right nnrat]
       ['left-positive (positive 'left)]
       ['right-positive (positive 'right)]]
      (app
       (app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        (function/lam
         [['ignored (bool-equality decision false-value)]]
         'right-positive)
        (function/lam
         [['ignored (bool-equality decision true-value)]]
         'left-positive)
        decision)
       (app (function/const* 'equality/reflexive [type-level])
            bool decision)))}))

(def reciprocal-positive-spec
  {:name 'nnrat/reciprocal-positive
   :universes []
   :type
   (function/forall
    [['value nnrat]]
    (positive (reciprocal 'value)))
   :value
   (function/lam
    [['value nnrat]]
    (let [previous (denominator-predecessor 'value)
          positive-numerator (successor previous)]
      (app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam
        [['extra nat]]
        (nat-equality (nat-add (successor nat-zero) 'extra)
                      positive-numerator))
       previous
       (nat-reflexive positive-numerator))))})

(def divide-positive-left-spec
  {:name 'nnrat/divide-positive-left
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]]
    (positive (divide 'left 'right)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['left-positive (positive 'left)]]
    (app
     (function/const* 'nnrat/multiply-positive [])
     'left (reciprocal 'right)
     'left-positive
     (app (function/const* 'nnrat/reciprocal-positive []) 'right)))})

(def definition-specs [positive-spec])
(def theorem-specs
  [one-positive-spec multiply-positive-spec positive-respects-equivalence-spec
   nat-add-positive-left-spec
   denominator-positive-spec add-positive-left-spec add-positive-right-spec
   min-positive-spec
   reciprocal-positive-spec divide-positive-left-spec])

(defn- extend-spec-if-missing [env alias spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env :nnrat-positive-support [spec])))

(defn extend-environment [env]
  (-> env
      (extend-spec-if-missing
       'nat/multiply-right-strict-monotone-positive
       bellman/multiply-right-strict-monotone-positive-spec)
      (extend-spec-if-missing
       'nat/multiply-successor-right-cancel
       semiring/multiply-successor-right-cancel-spec)
      (extend-spec-if-missing
       'nat/positive-of-nonzero
       separation/positive-of-nonzero-spec)
      (extend-spec-if-missing
       'nat/nonzero-of-positive
       separation/nonzero-of-positive-spec)
      (extend-spec-if-missing
       'nnrat/add-commutative
       add-monotone/add-commutative-spec)
      (extend-spec-if-missing 'minmax/min minmax/min-spec)
      (extend-spec-if-missing 'nnrat/reciprocal division/reciprocal-spec)
      (extend-spec-if-missing 'nnrat/divide division/divide-spec)
      (support/extend-with
       :nnrat-positive (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
