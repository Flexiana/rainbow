(ns rainbow.math.rational.signed.minmax
  "Universal minimum and maximum over signed rationals.

  The older validation/STL layer computes signed extrema under validation-specific
  aliases and proves only which operand is selected in one Boolean branch.  This
  module exposes reusable signed/min and signed/max operations and proves their
  actual order laws for every pair of signed rationals:

    min a b <= a                 a <= max a b
    min a b <= b                 b <= max a b
    lo <= x, lo <= y -> lo <= min x y
    x <= hi, y <= hi -> max x y <= hi

  Each proof case-splits on signed/decide-at-most.  Its true and false soundness
  theorems supply the only non-reflexive order fact needed in either branch.
  Native and axiom-free on D63."
  (:refer-clojure :exclude [min max])
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def bool (function/const* 'data/Bool []))
(def signed (function/const* 'signed/SignedRational []))
(def false-value (function/const* 'data/false []))
(def true-value (function/const* 'data/true []))

(defn- app [f & args] (apply function/app f args))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- decide-at-most [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- at-most [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- selected-at [at-false at-true choice]
  (app (function/const* 'data/Bool.rec [type-level])
       (function/lam [['ignored bool]] signed)
       at-false at-true choice))
(defn- minimum [left right]
  (app (function/const* 'signed/min []) left right))
(defn- maximum [left right]
  (app (function/const* 'signed/max []) left right))

(def min-spec
  {:name 'signed/min :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed)
   :value
   (function/lam
    [['left signed] ['right signed]]
    ;; false means right <= left, true means left <= right
    (selected-at 'right 'left (decide-at-most 'left 'right)))})

(def max-spec
  {:name 'signed/max :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed signed)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (selected-at 'left 'right (decide-at-most 'left 'right)))})

(def definition-specs [min-spec max-spec])

(defn- reflexive-equality [carrier value]
  (app (function/const* 'equality/reflexive [type-level]) carrier value))
(defn- at-most-reflexive [value]
  (app (function/const* 'signed/at-most-reflexive []) value))
(defn- decide-true-sound [left right decided]
  (app (function/const* 'signed/decide-at-most-true-sound [])
       left right decided))
(defn- decide-false-reverse [left right decided]
  (app (function/const* 'signed/decide-at-most-false-reverse [])
       left right decided))

(defn- case-split
  "Prove a goal about a selected signed value by splitting the order decision."
  [left right at-false at-true goal-of false-proof true-proof]
  (let [decision (decide-at-most left right)
        motive
        (function/lam
         [['choice bool]]
         (function/arrow
          (eq-bool decision 'choice)
          (goal-of (selected-at at-false at-true 'choice))))]
    (app
     (app (function/const* 'data/Bool.rec [zero-level])
          motive
          (function/lam [['h (eq-bool decision false-value)]]
                        (false-proof 'h))
          (function/lam [['h (eq-bool decision true-value)]]
                        (true-proof 'h))
          decision)
     (reflexive-equality bool decision))))

(def min-lower-left-spec
  {:name 'signed/min-lower-left :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (at-most (minimum 'left 'right) 'left))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (case-split
     'left 'right 'right 'left
     (fn [selected] (at-most selected 'left))
     (fn [h] (decide-false-reverse 'left 'right h))
     (fn [_] (at-most-reflexive 'left))))})

(def min-lower-right-spec
  {:name 'signed/min-lower-right :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (at-most (minimum 'left 'right) 'right))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (case-split
     'left 'right 'right 'left
     (fn [selected] (at-most selected 'right))
     (fn [_] (at-most-reflexive 'right))
     (fn [h] (decide-true-sound 'left 'right h))))})

(def max-upper-left-spec
  {:name 'signed/max-upper-left :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (at-most 'left (maximum 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (case-split
     'left 'right 'left 'right
     (fn [selected] (at-most 'left selected))
     (fn [_] (at-most-reflexive 'left))
     (fn [h] (decide-true-sound 'left 'right h))))})

(def max-upper-right-spec
  {:name 'signed/max-upper-right :universes []
   :type
   (function/forall
    [['left signed] ['right signed]]
    (at-most 'right (maximum 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]]
    (case-split
     'left 'right 'left 'right
     (fn [selected] (at-most 'right selected))
     (fn [h] (decide-false-reverse 'left 'right h))
     (fn [_] (at-most-reflexive 'right))))})

(def at-most-min-spec
  {:name 'signed/at-most-min :universes []
   :type
   (function/forall
    [['lower signed] ['left signed] ['right signed]
     ['lower-left (at-most 'lower 'left)]
     ['lower-right (at-most 'lower 'right)]]
    (at-most 'lower (minimum 'left 'right)))
   :value
   (function/lam
    [['lower signed] ['left signed] ['right signed]
     ['lower-left (at-most 'lower 'left)]
     ['lower-right (at-most 'lower 'right)]]
    (case-split
     'left 'right 'right 'left
     (fn [selected] (at-most 'lower selected))
     (fn [_] 'lower-right)
     (fn [_] 'lower-left)))})

(def at-most-max-spec
  {:name 'signed/at-most-max :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['upper signed]
     ['left-upper (at-most 'left 'upper)]
     ['right-upper (at-most 'right 'upper)]]
    (at-most (maximum 'left 'right) 'upper))
   :value
   (function/lam
    [['left signed] ['right signed] ['upper signed]
     ['left-upper (at-most 'left 'upper)]
     ['right-upper (at-most 'right 'upper)]]
    (case-split
     'left 'right 'left 'right
     (fn [selected] (at-most selected 'upper))
     (fn [_] 'left-upper)
     (fn [_] 'right-upper)))})

(def theorem-specs
  [min-lower-left-spec min-lower-right-spec
   max-upper-left-spec max-upper-right-spec
   at-most-min-spec at-most-max-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.decide-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-minmax (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.minmax))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
