(ns rainbow.math.rational.nnrat.order-total
  "Totality of the nnrat order: for all a b, a <= b OR b <= a.

  A prerequisite for the recursive-reduction sub-brick of the general LP
  Fourier-Motzkin encoding: reducing a
  both-sides cross row A*v + P <= B*v + Q to an affine row needs to
  case-split on A vs B, and the both-sides->upper direction needs B <= A
  from the failure of A <= B -- which requires the order to be TOTAL, not
  merely decidable. nnrat/at-most-decidable gives a <= b OR NOT (a <= b);
  this gives a <= b OR b <= a.

  Proof mirrors nnrat/at-most-decidable but the false branch yields the
  reverse inequality instead of a negation: case on the boolean decision
  audit/decide-nnrat-at-most a b (Bool.rec with the standard equality
  motive), true -> a <= b (nnrat/decide-at-most-true-sound), false ->
  b <= a (nnrat/decide-at-most-false-reverse). Native proof data,
  axiom-free."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.finite.rational-argmax :as argmax]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

(defn- at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))
(defn- disjunction [left right]
  (function/app (function/const* 'proposition/disjunction []) left right))
(defn- left-disjunct [left right evidence]
  (function/app (function/const* 'proposition/left-disjunct []) left right evidence))
(defn- right-disjunct [left right evidence]
  (function/app (function/const* 'proposition/right-disjunct []) left right evidence))
(defn- decide [a b]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) a b))
(defn- eq [x y]
  (function/equality type-level bool x y))
(defn- reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level]) bool value))
(defn- true-sound [a b same]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound []) a b same))
(defn- false-reverse [a b same]
  (function/app (function/const* 'nnrat/decide-at-most-false-reverse []) a b same))

(def at-most-total-spec
  {:name 'nnrat/at-most-total
   :universes []
   :type
   (function/forall
    [['a nnrat] ['b nnrat]]
    (disjunction (at-most 'a 'b) (at-most 'b 'a)))
   :value
   (function/lam
    [['a nnrat] ['b nnrat]]
    (let [claim-l (at-most 'a 'b)
          claim-r (at-most 'b 'a)
          decision (decide 'a 'b)
          motive (function/lam
                  [['choice bool]]
                  (function/arrow (eq decision 'choice)
                                  (disjunction claim-l claim-r)))]
      (function/app
       (function/app
        (function/const* 'data/Bool.rec [zero-level])
        motive
        ;; false: decision = false -> b <= a
        (function/lam
         [['same-false (eq decision false-value)]]
         (right-disjunct claim-l claim-r (false-reverse 'a 'b 'same-false)))
        ;; true: decision = true -> a <= b
        (function/lam
         [['same-true (eq decision true-value)]]
         (left-disjunct claim-l claim-r (true-sound 'a 'b 'same-true)))
        decision)
       (reflexive decision))))})

(def definition-specs [])
(def theorem-specs [at-most-total-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.rational-argmax])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-order-total (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.order-total))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
