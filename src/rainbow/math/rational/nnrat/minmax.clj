(ns rainbow.math.rational.nnrat.minmax
  "General exact-rational min/max with UNIVERSAL (forall-quantified) order guarantees.

  Unlike the worked-instance selection proofs in the AHoF catalog (which fix concrete
  operands), these theorems hold for ALL nonnegative-rational operands:

      min a b = if (a <= b) then a else b
      max a b = if (a <= b) then b else a

  Proved for all a, b:
    min-lower-left    : min a b <= a
    min-lower-right   : min a b <= b
    max-upper-left    : a <= max a b
    max-upper-right   : b <= max a b
    at-most-min       : lo <= x -> lo <= y -> lo <= min x y   (greatest-lower-bound step)
    at-most-max       : x <= hi -> y <= hi -> max x y <= hi   (least-upper-bound step)

  The proofs case-split on the decidable order via data/Bool.rec with an equality
  motive, discharging the true branch by nnrat/decide-at-most-true-sound and the false
  branch by nnrat/decide-at-most-false-reverse -- the standard Rainbow decide case-split.
  Native and axiom-free."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(defn- decide-at-most [l r]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) l r))
(defn- at-most [l r]
  (function/app (function/const* 'nnrat/at-most []) l r))
(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level]) carrier value))
(defn- eq-bool [l r] (function/equality type-level bool l r))

;; selected-at left right choice : returns left when choice=false, right when choice=true
(defn- selected-at [left right choice]
  (function/app (function/const* 'data/Bool.rec [type-level])
                (function/lam [['ignored bool]] nnrat)
                left right choice))

;; min a b = selected-at b a (a<=b): false(a>b)->b, true(a<=b)->a  (the smaller)
(defn- minimum [a b] (function/app (function/const* 'minmax/min []) a b))
;; max a b = selected-at a b (a<=b): false(a>b)->a, true(a<=b)->b  (the larger)
(defn- maximum [a b] (function/app (function/const* 'minmax/max []) a b))

(def min-spec
  {:name 'minmax/min :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (selected-at 'b 'a (decide-at-most 'a 'b)))})

(def max-spec
  {:name 'minmax/max :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['a nnrat] ['b nnrat]]
                        (selected-at 'a 'b (decide-at-most 'a 'b)))})

(def definition-specs [min-spec max-spec])

;; ---- helpers to build a case-split proof over decide(a<=b) ----
(defn- decide-true-sound [a b same]
  (function/app (function/const* 'nnrat/decide-at-most-true-sound []) a b same))
(defn- decide-false-reverse [a b same]
  (function/app (function/const* 'nnrat/decide-at-most-false-reverse []) a b same))
(defn- at-most-reflexive [v]
  (function/app (function/const* 'nnrat/at-most-reflexive []) v))

;; Generic case-split: prove  (goal-of (selected-at s-false s-true decision))
;; where decision = decide(a<=b), given false-branch and true-branch proofs.
;; motive choice = (eq decision choice) -> (goal-of (selected-at s-false s-true choice))
(defn- case-split [a b s-false s-true goal-of false-proof true-proof]
  (let [decision (decide-at-most a b)
        motive (function/lam
                [['choice bool]]
                (function/arrow (eq-bool decision 'choice)
                                (goal-of (selected-at s-false s-true 'choice))))]
    (function/app
     (function/app
      (function/const* 'data/Bool.rec [zero-level])
      motive
      (function/lam [['h (eq-bool decision false-value)]] (false-proof 'h))
      (function/lam [['h (eq-bool decision true-value)]] (true-proof 'h))
      decision)
     (reflexive type-level bool decision))))

;; ---- min bounds ----
;; min a b <= a
(def min-lower-left-spec
  {:name 'minmax/min-lower-left :universes []
   :type (function/forall [['a nnrat] ['b nnrat]] (at-most (minimum 'a 'b) 'a))
   :value (function/lam
           [['a nnrat] ['b nnrat]]
           ;; min = selected-at b a decision ; goal: at-most selected a
           (case-split 'a 'b 'b 'a
                       (fn [sel] (at-most sel 'a))
                       ;; false: sel=b, need b<=a  (decide false -> b<=a)
                       (fn [h] (decide-false-reverse 'a 'b h))
                       ;; true: sel=a, need a<=a
                       (fn [h] (at-most-reflexive 'a))))})

;; min a b <= b
(def min-lower-right-spec
  {:name 'minmax/min-lower-right :universes []
   :type (function/forall [['a nnrat] ['b nnrat]] (at-most (minimum 'a 'b) 'b))
   :value (function/lam
           [['a nnrat] ['b nnrat]]
           (case-split 'a 'b 'b 'a
                       (fn [sel] (at-most sel 'b))
                       ;; false: sel=b, need b<=b
                       (fn [h] (at-most-reflexive 'b))
                       ;; true: sel=a, need a<=b (decide true -> a<=b)
                       (fn [h] (decide-true-sound 'a 'b h))))})

;; ---- max bounds ----
;; a <= max a b
(def max-upper-left-spec
  {:name 'minmax/max-upper-left :universes []
   :type (function/forall [['a nnrat] ['b nnrat]] (at-most 'a (maximum 'a 'b)))
   :value (function/lam
           [['a nnrat] ['b nnrat]]
           ;; max = selected-at a b decision ; goal: at-most a selected
           (case-split 'a 'b 'a 'b
                       (fn [sel] (at-most 'a sel))
                       ;; false: sel=a, need a<=a
                       (fn [h] (at-most-reflexive 'a))
                       ;; true: sel=b, need a<=b
                       (fn [h] (decide-true-sound 'a 'b h))))})

;; b <= max a b
(def max-upper-right-spec
  {:name 'minmax/max-upper-right :universes []
   :type (function/forall [['a nnrat] ['b nnrat]] (at-most 'b (maximum 'a 'b)))
   :value (function/lam
           [['a nnrat] ['b nnrat]]
           (case-split 'a 'b 'a 'b
                       (fn [sel] (at-most 'b sel))
                       ;; false: sel=a, need b<=a (decide false -> b<=a)
                       (fn [h] (decide-false-reverse 'a 'b h))
                       ;; true: sel=b, need b<=b
                       (fn [h] (at-most-reflexive 'b))))})

;; ---- lattice steps ----
;; lo <= x -> lo <= y -> lo <= min x y
(def at-most-min-spec
  {:name 'minmax/at-most-min :universes []
   :type (function/forall
          [['lo nnrat] ['x nnrat] ['y nnrat]
           ['lo-x (at-most 'lo 'x)] ['lo-y (at-most 'lo 'y)]]
          (at-most 'lo (minimum 'x 'y)))
   :value (function/lam
           [['lo nnrat] ['x nnrat] ['y nnrat]
            ['lo-x (at-most 'lo 'x)] ['lo-y (at-most 'lo 'y)]]
           ;; min x y = selected-at y x (x<=y): false->y, true->x
           (case-split 'x 'y 'y 'x
                       (fn [sel] (at-most 'lo sel))
                       (fn [h] 'lo-y)   ;; false: sel=y
                       (fn [h] 'lo-x)))});; true: sel=x

;; x <= hi -> y <= hi -> max x y <= hi
(def at-most-max-spec
  {:name 'minmax/at-most-max :universes []
   :type (function/forall
          [['x nnrat] ['y nnrat] ['hi nnrat]
           ['x-hi (at-most 'x 'hi)] ['y-hi (at-most 'y 'hi)]]
          (at-most (maximum 'x 'y) 'hi))
   :value (function/lam
           [['x nnrat] ['y nnrat] ['hi nnrat]
            ['x-hi (at-most 'x 'hi)] ['y-hi (at-most 'y 'hi)]]
           ;; max x y = selected-at x y (x<=y): false->x, true->y
           (case-split 'x 'y 'x 'y
                       (fn [sel] (at-most sel 'hi))
                       (fn [h] 'x-hi)   ;; false: sel=x
                       (fn [h] 'y-hi)))});; true: sel=y

(def theorem-specs
  [min-lower-left-spec min-lower-right-spec max-upper-left-spec max-upper-right-spec
   at-most-min-spec at-most-max-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-minmax
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
