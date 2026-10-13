(ns rainbow.math.rational.signed.structural-equality
  "Decidable STRUCTURAL equality for nonnegative and signed rationals.

  `signed/decide-equivalent` decides the QUOTIENT: 1/2 and 2/4 embed as
  different pairs that it correctly calls equivalent.  Some checks need the opposite
  instrument: structural equality, under which two values are equal exactly when
  they carry the SAME pair.

  A signed value is a pair of nonnegative rationals, each a pair of unary
  naturals, so the decision is four `nat/decide-equality` calls under two
  `boolean/and`, and the proofs are assembled from parts that all exist:
  and-elimination, the nat decision's soundness and reflexivity, `product/eta`
  for reconstruction, and two-step congruence for the pair constructors.

  Both directions are proved at both layers -- a true verdict IS structural
  equality and structural equality FORCES a true verdict -- so a decision built
  on top of it is honest in both outcomes.

  Native and axiom-free."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.linear.matrix.row-length-decider :as nat-decider]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def true-value (function/const* 'data/true []))

(defn- app [f & args] (apply function/app f args))
(defn- eq-of [carrier left right]
  (function/equality type-level carrier left right))
(defn- eq-bool [left right] (eq-of bool left right))
(defn- both [left right]
  (app (function/const* 'boolean/and []) left right))
(defn- decide-nat [left right]
  (app (function/const* 'nat/decide-equality []) left right))
(defn- numerator-of [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- denominator-predecessor-of [value]
  (app (function/const* 'nnrat/denominator-predecessor []) value))
(defn- positive-of [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative-of [value]
  (app (function/const* 'signed/negative []) value))
(defn- nnrat-make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- signed-make [positive negative]
  (app (function/const* 'signed/make []) positive negative))
(defn- transitive [carrier x y z proof-xy proof-yz]
  (app (function/const* 'equality/transitive [type-level])
       carrier x y z proof-xy proof-yz))
(defn- symmetric [carrier x y proof]
  (app (function/const* 'equality/symmetric [type-level]) carrier x y proof))
(defn- congruent [domain codomain f x y proof]
  (app (function/const* 'equality/congruent-function [type-level type-level])
       domain codomain f x y proof))
(defn- product-eta [value]
  ;; product/eta's binders are ['A [:sort [:succ u]]], so the universe ARGUMENT
  ;; for a Type-0 carrier is zero, not type-level -- the succ is in the binder.
  (app (function/const* 'product/eta [zero-level zero-level]) nat nat value))
(defn- signed-product-eta [value]
  (app (function/const* 'product/eta [zero-level zero-level]) nnrat nnrat value))

;; ---- the decisions ----------------------------------------------------------

(def nnrat-decide-spec
  {:name 'nnrat/decide-structural-equal :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow nnrat nnrat bool)
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (both (decide-nat (numerator-of 'left) (numerator-of 'right))
          (decide-nat (denominator-predecessor-of 'left)
                      (denominator-predecessor-of 'right))))})

(defn- decide-nnrat [left right]
  (app (function/const* 'nnrat/decide-structural-equal []) left right))

(def signed-decide-spec
  {:name 'signed/decide-structural-equal :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed bool)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (both (decide-nnrat (positive-of 'left) (positive-of 'right))
          (decide-nnrat (negative-of 'left) (negative-of 'right))))})

(defn- decide-signed [left right]
  (app (function/const* 'signed/decide-structural-equal []) left right))

;; ---- reconstruction ---------------------------------------------------------

(def nnrat-reconstruct-spec
  "make (numerator r) (denominator-predecessor r) IS pair (first r) (second r)
  definitionally, so product/eta closes this. Stated at the nnrat carrier so
  users never have to unfold the representation."
  {:name 'nnrat/reconstruct :universes []
   :type
   (function/forall
    [['value nnrat]]
    (eq-of nnrat
           (nnrat-make (numerator-of 'value)
                       (denominator-predecessor-of 'value))
           'value))
   :value (function/lam [['value nnrat]] (product-eta 'value))})

(def signed-reconstruct-spec
  {:name 'signed/reconstruct :universes []
   :type
   (function/forall
    [['value signed]]
    (eq-of signed
           (signed-make (positive-of 'value) (negative-of 'value))
           'value))
   :value (function/lam [['value signed]] (signed-product-eta 'value))})

;; ---- soundness, reflexivity, completeness, generically ----------------------

(defn- pairwise-soundness
  "true verdict => structural equality, for a carrier that is a pair.

  Shape shared by both layers: split the AND, apply the field decision's
  soundness to each half, rebuild with two congruence steps through the
  constructor, and close both ends with reconstruction."
  [{:keys [theorem-name carrier field-carrier decide field-decide
           field-sound first-of second-of make reconstruct]}]
  (let [left-first (first-of 'left) left-second (second-of 'left)
        right-first (first-of 'right) right-second (second-of 'right)
        verdict (eq-bool (decide 'left 'right) true-value)
        first-verdict (eq-bool (field-decide left-first right-first) true-value)
        second-verdict (eq-bool (field-decide left-second right-second) true-value)]
    {:name theorem-name :universes []
     :type (function/forall [['left carrier] ['right carrier]]
                            (function/arrow verdict (eq-of carrier 'left 'right)))
     :value
     (function/lam
      [['left carrier] ['right carrier] ['verdict verdict]]
      (let [firsts (field-sound left-first right-first
                                (app (function/const* 'boolean/and-implies-left [])
                                     (field-decide left-first right-first)
                                     (field-decide left-second right-second)
                                     'verdict))
            seconds (field-sound left-second right-second
                                 (app (function/const* 'boolean/and-implies-right [])
                                      (field-decide left-first right-first)
                                      (field-decide left-second right-second)
                                      'verdict))
            left-rebuilt (make left-first left-second)
            mixed (make right-first left-second)
            right-rebuilt (make right-first right-second)
            step-one (congruent field-carrier carrier
                                (function/lam [['field field-carrier]]
                                              (make 'field left-second))
                                left-first right-first firsts)
            step-two (congruent field-carrier carrier
                               (function/lam [['field field-carrier]]
                                             (make right-first 'field))
                               left-second right-second seconds)
            across (transitive carrier left-rebuilt mixed right-rebuilt
                               step-one step-two)]
        (transitive carrier 'left left-rebuilt 'right
                    (symmetric carrier left-rebuilt 'left (reconstruct 'left))
                    (transitive carrier left-rebuilt right-rebuilt 'right
                                across (reconstruct 'right)))))}))

(defn- pairwise-reflexivity
  "decide v v computes true, because each field decision is reflexive-true and
  AND of two trues introduces true."
  [{:keys [theorem-name carrier decide field-decide field-reflexive
           first-of second-of]}]
  {:name theorem-name :universes []
   :type (function/forall [['value carrier]]
                          (eq-bool (decide 'value 'value) true-value))
   :value
   (function/lam
    [['value carrier]]
    (app (function/const* 'boolean/and-true-introduction [])
         (field-decide (first-of 'value) (first-of 'value))
         (field-decide (second-of 'value) (second-of 'value))
         (field-reflexive (first-of 'value))
         (field-reflexive (second-of 'value))))})

(defn- pairwise-completeness
  "structural equality forces a true verdict: transport reflexivity along the
  equality, which is one Leibniz application."
  [{:keys [theorem-name carrier decide reflexive-name]}]
  {:name theorem-name :universes []
   :type (function/forall [['left carrier] ['right carrier]]
                          (function/arrow (eq-of carrier 'left 'right)
                                          (eq-bool (decide 'left 'right)
                                                   true-value)))
   :value
   (function/lam
    [['left carrier] ['right carrier] ['same (eq-of carrier 'left 'right)]]
    (app 'same
         (function/lam [['other carrier]]
                       (eq-bool (decide 'left 'other) true-value))
         (app (function/const* reflexive-name []) 'left)))})

(def nnrat-layer
  {:carrier nnrat :field-carrier nat
   :decide decide-nnrat :field-decide decide-nat
   :field-sound (fn [x y proof]
                  (app (function/const* 'nat/decide-equality-true-sound [])
                       x y proof))
   :field-reflexive (fn [x]
                      (app (function/const* 'nat/decide-equality-reflexive-true [])
                           x))
   :first-of numerator-of :second-of denominator-predecessor-of
   :make nnrat-make
   :reconstruct (fn [v] (app (function/const* 'nnrat/reconstruct []) v))})

(def signed-layer
  {:carrier signed :field-carrier nnrat
   :decide decide-signed :field-decide decide-nnrat
   :field-sound (fn [x y proof]
                  (app (function/const* 'nnrat/decide-structural-equal-true-sound [])
                       x y proof))
   :field-reflexive (fn [x]
                      (app (function/const*
                            'nnrat/decide-structural-equal-reflexive-true [])
                           x))
   :first-of positive-of :second-of negative-of
   :make signed-make
   :reconstruct (fn [v] (app (function/const* 'signed/reconstruct []) v))})

(def theorem-specs
  [nnrat-reconstruct-spec
   signed-reconstruct-spec
   (pairwise-soundness
    (assoc nnrat-layer :theorem-name 'nnrat/decide-structural-equal-true-sound))
   (pairwise-reflexivity
    (assoc nnrat-layer :theorem-name 'nnrat/decide-structural-equal-reflexive-true))
   (pairwise-completeness
    (assoc nnrat-layer :theorem-name 'nnrat/decide-structural-equal-true-complete
           :reflexive-name 'nnrat/decide-structural-equal-reflexive-true))
   (pairwise-soundness
    (assoc signed-layer :theorem-name 'signed/decide-structural-equal-true-sound))
   (pairwise-reflexivity
    (assoc signed-layer :theorem-name 'signed/decide-structural-equal-reflexive-true))
   (pairwise-completeness
    (assoc signed-layer :theorem-name 'signed/decide-structural-equal-true-complete
           :reflexive-name 'signed/decide-structural-equal-reflexive-true))])

(def definition-specs [nnrat-decide-spec signed-decide-spec])

(defn- extend-with-product-eta-if-missing [checked-environment]
  (if (environment/resolve-id checked-environment 'product/eta)
    checked-environment
    (throw (ex-info "product/eta is absent; chain the module that installs it"
                    {:missing 'product/eta}))))

(defn extend-environment [checked-environment]
  (-> checked-environment
      boolean-and/extend-environment
      nat-decider/extend-environment
      extend-with-product-eta-if-missing
      (support/extend-with :signed-structural-equality
                           (concat definition-specs theorem-specs))))

(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
