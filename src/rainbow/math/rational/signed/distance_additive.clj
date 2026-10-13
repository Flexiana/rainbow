(ns rainbow.math.rational.signed.distance-additive
  "Paired-addition Lipschitz law for quotient-safe signed distance.

  The triangle inequality splits through a mixed sum.  Right translation
  cancels the unchanged second addend on the first leg, left translation
  cancels the unchanged first addend on the second leg, and order congruence
  transports the resulting upper bound.  This is the scalar induction step
  for dot-product distance estimates.  Native, kernel-checked, and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.distance-translation :as translation]
            [rainbow.math.rational.signed.distance-triangle :as triangle]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))

(def distance-add-spec
  {:name 'signed/distance-add :universes []
   :type
   (function/forall
    [['left-first signed] ['left-second signed]
     ['right-first signed] ['right-second signed]]
    (sle
     (scalar-distance
      (add 'left-first 'left-second)
      (add 'right-first 'right-second))
     (add (scalar-distance 'left-first 'right-first)
          (scalar-distance 'left-second 'right-second))))
   :value
   (function/lam
    [['left-first signed] ['left-second signed]
     ['right-first signed] ['right-second signed]]
    (let [source
          (scalar-distance
           (add 'left-first 'left-second)
           (add 'right-first 'right-second))
          bridge (add 'right-first 'left-second)
          first-leg
          (scalar-distance
           (add 'left-first 'left-second) bridge)
          second-leg
          (scalar-distance
           bridge (add 'right-first 'right-second))
          legs (add first-leg second-leg)
          first-target
          (scalar-distance 'left-first 'right-first)
          second-target
          (scalar-distance 'left-second 'right-second)
          target (add first-target second-target)
          triangle-bound
          (app (function/const* 'signed/distance-triangle [])
               (add 'left-first 'left-second)
               bridge
               (add 'right-first 'right-second))
          legs-same
          (app
           (function/const* 'signed/add-respects-equivalence [])
           first-leg first-target second-leg second-target
           (app (function/const* 'signed/distance-add-right [])
                'left-first 'right-first 'left-second)
           (app (function/const* 'signed/distance-add-left [])
                'right-first 'left-second 'right-second))]
      (order-respects
       source source legs target
       (equivalent-reflexive source)
       legs-same
       triangle-bound)))})

(def definition-specs [])
(def theorem-specs [distance-add-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :signed-distance-additive theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.rational.signed.distance-additive))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
