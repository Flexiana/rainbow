(ns rainbow.math.rational.signed.decide-completeness
  "Completeness of Rainbow's exact-rational decision procedures.

  The existing decision bridge is sound: a computation returning true yields
  the corresponding order or signed-equivalence proof.  This module proves the
  converse for EVERY value, and then proves that a false result refutes the
  corresponding proposition. Consequently `signed/decide-equivalent` is a
  complete two-outcome proof-producing test for the Grothendieck equivalence of
  signed rationals, not merely a sound filter observed on concrete numerals.

  The proof follows the implementation boundary exactly.  Nat completeness
  uses total Boolean case analysis, order antisymmetry, and the already-proved
  true-on-reflexive comparison.  Nnrat completeness transports an order proof
  to the two natural cross products.  Signed completeness applies the nnrat
  result to the signed cross sums.  Equivalence completeness proves both signed
  orders and combines the two true decisions.  Native and axiom-free on D63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.algorithms.proofs.bellman-scaled-fixed-point-uniqueness :as bellman-uniqueness]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.finite.metric-separation :as finite-separation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-equivalence :as nnrat-order]
            [rainbow.math.rational.signed.decide-equivalence :as decide-equivalence]
            [rainbow.math.rational.signed.decide-reflexive :as decide-reflexive]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))
(defn- eq-bool [left right] (equality bool left right))
(defn- reflexive [carrier value]
  (app (function/const* 'equality/reflexive [type-level]) carrier value))
(defn- symmetric [carrier left right same]
  (app (function/const* 'equality/symmetric [type-level])
       carrier left right same))
(defn- transitive [carrier left middle right first second]
  (app (function/const* 'equality/transitive [type-level])
       carrier left middle right first second))
(defn- congruent [source target mapping left right same]
  (app (function/const* 'equality/congruent-function
                        [type-level type-level])
       source target mapping left right same))

(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- decide-nat [left right]
  (app (function/const* 'nat/decide-at-most []) left right))
(defn- numerator [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- multiply-nat [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- nnrat-at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- decide-nnrat [left right]
  (app (function/const* 'audit/decide-nnrat-at-most []) left right))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- add-nnrat [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- signed-at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- decide-signed [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- signed-equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- decide-signed-equivalent [left right]
  (app (function/const* 'signed/decide-equivalent []) left right))
(defn- bool-and [left right]
  (app (function/const* 'boolean/and []) left right))
(defn- falsity [] (function/const* 'proposition/falsity []))

(defn- false-refutation
  "Given decision=false and decision=true, derive False by constructor
  discrimination. Kept as a proof-term helper rather than a declaration."
  [decision decided-false decided-true]
  (app
   (function/const* 'bool/false-not-true [])
   (transitive bool false-value decision true-value
               (symmetric bool decision false-value decided-false)
               decided-true)))

(defn- false-complete-proof
  "Case-split a Boolean decision. The false branch is reflexive; the true
  branch contradicts a supplied refutation using the decision's soundness."
  [decision proposition refutes true-proof]
  (let [goal (eq-bool decision false-value)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow (eq-bool decision 'choice)
                         (eq-bool 'choice false-value)))
        false-case
        (function/lam
         [['ignored (eq-bool decision false-value)]]
         (reflexive bool false-value))
        true-case
        (function/lam
         [['decided-true (eq-bool decision true-value)]]
         (app (function/const* 'proposition/explode [])
              (eq-bool true-value false-value)
              (app refutes (true-proof 'decided-true))))]
    (app
     (app (function/const* 'data/Bool.rec [zero-level])
          motive false-case true-case decision)
     (reflexive bool decision))))

(def boolean-and-true-complete-spec
  {:name 'boolean/and-true-complete :universes []
   :type
   (function/forall
    [['left bool] ['right bool]
     ['left-true (eq-bool 'left true-value)]
     ['right-true (eq-bool 'right true-value)]]
    (eq-bool (bool-and 'left 'right) true-value))
   :value
   (function/lam
    [['left bool] ['right bool]
     ['left-true (eq-bool 'left true-value)]
     ['right-true (eq-bool 'right true-value)]]
    (let [left-step
          (congruent bool bool
                     (function/lam [['candidate bool]]
                                   (bool-and 'candidate 'right))
                     'left true-value 'left-true)
          right-step
          (congruent bool bool
                     (function/lam [['candidate bool]]
                                   (bool-and true-value 'candidate))
                     'right true-value 'right-true)]
      (transitive bool
                  (bool-and 'left 'right)
                  (bool-and true-value 'right)
                  true-value
                  left-step right-step)))})

(def nat-decide-at-most-true-complete-spec
  {:name 'nat/decide-at-most-true-complete :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['ordered (nat-at-most 'left 'right)]]
    (eq-bool (decide-nat 'left 'right) true-value))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['ordered (nat-at-most 'left 'right)]]
    (let [decision (decide-nat 'left 'right)
          goal (eq-bool decision true-value)
          motive
          (function/lam
           [['choice bool]]
           (function/arrow (eq-bool decision 'choice)
                           (eq-bool 'choice true-value)))
          false-case
          (function/lam
           [['decided-false (eq-bool decision false-value)]]
           (let [reverse-ordered
                 (app (function/const* 'nat/decide-at-most-false-reverse [])
                      'left 'right 'decided-false)
                 same
                 (app (function/const* 'nat/at-most-antisymmetric [])
                      'left 'right 'ordered reverse-ordered)
                 false-to-decision
                 (symmetric bool decision false-value 'decided-false)
                 decision-to-reflexive
                 (congruent nat bool
                            (function/lam [['candidate nat]]
                                          (decide-nat 'left 'candidate))
                            'right 'left
                            (symmetric nat 'left 'right same))
                 reflexive-to-true
                 (app (function/const*
                       'nat/decide-at-most-reflexive-true [])
                      'left)]
             (transitive
              bool false-value decision true-value
              false-to-decision
              (transitive bool decision
                          (decide-nat 'left 'left) true-value
                          decision-to-reflexive reflexive-to-true))))
          true-case
          (function/lam
           [['ignored (eq-bool decision true-value)]]
           (reflexive bool true-value))]
      (app
       (app (function/const* 'data/Bool.rec [zero-level])
            motive false-case true-case decision)
       (reflexive bool decision))))})

(def nnrat-decide-at-most-true-complete-spec
  {:name 'nnrat/decide-at-most-true-complete :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['ordered (nnrat-at-most 'left 'right)]]
    (eq-bool (decide-nnrat 'left 'right) true-value))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['ordered (nnrat-at-most 'left 'right)]]
    (let [left-cross
          (multiply-nat (numerator 'left) (denominator 'right))
          right-cross
          (multiply-nat (numerator 'right) (denominator 'left))]
      (app (function/const* 'nat/decide-at-most-true-complete [])
           left-cross right-cross
           (app (function/const* 'nnrat/at-most-to-cross [])
                'left 'right 'ordered))))})

(def signed-decide-at-most-true-complete-spec
  {:name 'signed/decide-at-most-true-complete :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['ordered (signed-at-most 'left 'right)]]
    (eq-bool (decide-signed 'left 'right) true-value))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['ordered (signed-at-most 'left 'right)]]
    (app (function/const* 'nnrat/decide-at-most-true-complete [])
         (add-nnrat (positive 'left) (negative 'right))
         (add-nnrat (positive 'right) (negative 'left))
         'ordered))})

(def signed-decide-equivalent-true-complete-spec
  {:name 'signed/decide-equivalent-true-complete :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (eq-bool (decide-signed-equivalent 'left 'right) true-value))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (let [forward
          (add-nnrat (positive 'left) (negative 'right))
          backward
          (add-nnrat (positive 'right) (negative 'left))
          left-right
          (app (function/const* 'nnrat/equivalent-to-at-most [])
               forward backward 'same)
          right-left-same
          (app (function/const* 'nnrat/equivalent-symmetric [])
               forward backward 'same)
          right-left
          (app (function/const* 'nnrat/equivalent-to-at-most [])
               backward forward right-left-same)
          forward-true
          (app (function/const* 'signed/decide-at-most-true-complete [])
               'left 'right left-right)
          backward-true
          (app (function/const* 'signed/decide-at-most-true-complete [])
               'right 'left right-left)]
      (app (function/const* 'boolean/and-true-complete [])
           (decide-signed 'left 'right)
           (decide-signed 'right 'left)
           forward-true backward-true)))})

(def nat-decide-at-most-false-sound-spec
  {:name 'nat/decide-at-most-false-sound :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['decided-false
      (eq-bool (decide-nat 'left 'right) false-value)]]
    (function/arrow (nat-at-most 'left 'right) (falsity)))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['decided-false
      (eq-bool (decide-nat 'left 'right) false-value)]
     ['ordered (nat-at-most 'left 'right)]]
    (false-refutation
     (decide-nat 'left 'right) 'decided-false
     (app (function/const* 'nat/decide-at-most-true-complete [])
          'left 'right 'ordered)))})

(def nnrat-decide-at-most-false-sound-spec
  {:name 'nnrat/decide-at-most-false-sound :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['decided-false
      (eq-bool (decide-nnrat 'left 'right) false-value)]]
    (function/arrow (nnrat-at-most 'left 'right) (falsity)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['decided-false
      (eq-bool (decide-nnrat 'left 'right) false-value)]
     ['ordered (nnrat-at-most 'left 'right)]]
    (false-refutation
     (decide-nnrat 'left 'right) 'decided-false
     (app (function/const* 'nnrat/decide-at-most-true-complete [])
          'left 'right 'ordered)))})

(def signed-decide-at-most-false-sound-spec
  {:name 'signed/decide-at-most-false-sound :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['decided-false
      (eq-bool (decide-signed 'left 'right) false-value)]]
    (function/arrow (signed-at-most 'left 'right) (falsity)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['decided-false
      (eq-bool (decide-signed 'left 'right) false-value)]
     ['ordered (signed-at-most 'left 'right)]]
    (false-refutation
     (decide-signed 'left 'right) 'decided-false
     (app (function/const* 'signed/decide-at-most-true-complete [])
          'left 'right 'ordered)))})

(def signed-decide-equivalent-false-sound-spec
  {:name 'signed/decide-equivalent-false-sound :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['decided-false
      (eq-bool (decide-signed-equivalent 'left 'right) false-value)]]
    (function/arrow (signed-equivalent 'left 'right) (falsity)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['decided-false
      (eq-bool (decide-signed-equivalent 'left 'right) false-value)]
     ['same (signed-equivalent 'left 'right)]]
    (false-refutation
     (decide-signed-equivalent 'left 'right) 'decided-false
     (app (function/const* 'signed/decide-equivalent-true-complete [])
          'left 'right 'same)))})

(def nat-decide-at-most-false-complete-spec
  {:name 'nat/decide-at-most-false-complete :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['not-ordered
      (function/arrow (nat-at-most 'left 'right) (falsity))]]
    (eq-bool (decide-nat 'left 'right) false-value))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['not-ordered
      (function/arrow (nat-at-most 'left 'right) (falsity))]]
    (false-complete-proof
     (decide-nat 'left 'right)
     (nat-at-most 'left 'right)
     'not-ordered
     (fn [decided-true]
       (app (function/const* 'nat/decide-at-most-true-sound [])
            'left 'right decided-true))))})

(def nnrat-decide-at-most-false-complete-spec
  {:name 'nnrat/decide-at-most-false-complete :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]
     ['not-ordered
      (function/arrow (nnrat-at-most 'left 'right) (falsity))]]
    (eq-bool (decide-nnrat 'left 'right) false-value))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]
     ['not-ordered
      (function/arrow (nnrat-at-most 'left 'right) (falsity))]]
    (false-complete-proof
     (decide-nnrat 'left 'right)
     (nnrat-at-most 'left 'right)
     'not-ordered
     (fn [decided-true]
       (app (function/const* 'nnrat/decide-at-most-true-sound [])
            'left 'right decided-true))))})

(def signed-decide-at-most-false-complete-spec
  {:name 'signed/decide-at-most-false-complete :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['not-ordered
      (function/arrow (signed-at-most 'left 'right) (falsity))]]
    (eq-bool (decide-signed 'left 'right) false-value))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['not-ordered
      (function/arrow (signed-at-most 'left 'right) (falsity))]]
    (false-complete-proof
     (decide-signed 'left 'right)
     (signed-at-most 'left 'right)
     'not-ordered
     (fn [decided-true]
       (app (function/const* 'signed/decide-at-most-true-sound [])
            'left 'right decided-true))))})

(def signed-decide-equivalent-false-complete-spec
  {:name 'signed/decide-equivalent-false-complete :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['not-same
      (function/arrow (signed-equivalent 'left 'right) (falsity))]]
    (eq-bool (decide-signed-equivalent 'left 'right) false-value))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['not-same
      (function/arrow (signed-equivalent 'left 'right) (falsity))]]
    (false-complete-proof
     (decide-signed-equivalent 'left 'right)
     (signed-equivalent 'left 'right)
     'not-same
     (fn [decided-true]
       (app (function/const* 'signed/decide-equivalent-true-sound [])
            'left 'right decided-true))))})

(def definition-specs [])
(def theorem-specs
  [boolean-and-true-complete-spec
   nat-decide-at-most-true-complete-spec
   nnrat-decide-at-most-true-complete-spec
   signed-decide-at-most-true-complete-spec
   signed-decide-equivalent-true-complete-spec
   nat-decide-at-most-false-sound-spec
   nnrat-decide-at-most-false-sound-spec
   signed-decide-at-most-false-sound-spec
   signed-decide-equivalent-false-sound-spec
   nat-decide-at-most-false-complete-spec
   nnrat-decide-at-most-false-complete-spec
   signed-decide-at-most-false-complete-spec
   signed-decide-equivalent-false-complete-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      decide-reflexive/extend-environment
      nnrat-order/extend-environment
      decide-equivalence/extend-environment
      boolean-and/extend-environment
      (support/extend-with :finite-metric-separation
                           [finite-separation/equal-zero-of-at-most-zero-spec])
      (support/extend-with
       :bellman-scaled-fixed-point-uniqueness
       [bellman-uniqueness/at-most-antisymmetric-spec])
      (support/extend-with :signed-decide-completeness theorem-specs)))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
