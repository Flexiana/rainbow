(ns rainbow.math.rational.signed.decide-equivalence
  "A computable, sound equality test for signed rationals.

  Signed rationals are Grothendieck pairs and their mathematical equality is
  `signed/equivalent`, not structural equality of the pairs.  Consequently a
  certificate generator must compare values in both order directions:

    signed/decide-equivalent a b
      = decide(a <= b) AND decide(b <= a)

  `signed/decide-equivalent-true-sound` turns a successful computation into the
  equivalence proof expected by optimality gaps and reported objective values.
  The proof projects both successful comparisons from Boolean conjunction,
  applies the signed-order decision soundness theorem twice, and closes with
  antisymmetry up to signed equivalence.

  This deliberately accepts different representations of the same rational
  (for example 1/2 and 2/4), while the kernel rejects a true-result witness for
  unequal values.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.decide-order :as decide-order]
            [rainbow.math.rational.signed.limit-uniqueness :as uniqueness]))

(def type-level [:succ [:zero]])
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))
(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & args] (apply function/app f args))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- equivalent [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- decide-at-most [left right]
  (app (function/const* 'signed/decide-at-most []) left right))
(defn- decide-equivalent [left right]
  (app (function/const* 'signed/decide-equivalent []) left right))
(defn- bool-and [left right]
  (app (function/const* 'boolean/and []) left right))

(def decide-equivalent-spec
  {:name 'signed/decide-equivalent :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow signed signed bool)
   :value
   (function/lam
    [['left signed] ['right signed]]
    (bool-and (decide-at-most 'left 'right)
              (decide-at-most 'right 'left)))})

(def decide-equivalent-true-sound-spec
  {:name 'signed/decide-equivalent-true-sound :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['decided (eq-bool (decide-equivalent 'left 'right) true-value)]]
    (equivalent 'left 'right))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['decided (eq-bool (decide-equivalent 'left 'right) true-value)]]
    (let [left<=right-decision
          (app (function/const* 'boolean/and-implies-left [])
               (decide-at-most 'left 'right)
               (decide-at-most 'right 'left)
               'decided)
          right<=left-decision
          (app (function/const* 'boolean/and-implies-right [])
               (decide-at-most 'left 'right)
               (decide-at-most 'right 'left)
               'decided)
          left<=right
          (app (function/const* 'signed/decide-at-most-true-sound [])
               'left 'right left<=right-decision)
          right<=left
          (app (function/const* 'signed/decide-at-most-true-sound [])
               'right 'left right<=left-decision)]
      (app (function/const* 'signed/at-most-antisymmetric [])
           'left 'right left<=right right<=left)))})

(def definition-specs [decide-equivalent-spec])
(def theorem-specs [decide-equivalent-true-sound-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.limit-uniqueness rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-order])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-decide-equivalence (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.decide-equivalence))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
