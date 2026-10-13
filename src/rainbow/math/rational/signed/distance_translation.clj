(ns rainbow.math.rational.signed.distance-translation
  "Translation invariance of quotient-safe signed distance.

  A verified NNRat ring certificate first cancels a common signed prefix from
  subtraction.  Absolute-value congruence lifts that identity to distance, and
  additive commutativity supplies the right-translation orientation.  These
  are the scalar cancellation laws required to remove the offset from affine
  sup-distance bounds.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.signed.distance :as distance]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- positive [value]
  (app (function/const* 'signed/positive []) value))
(defn- negative [value]
  (app (function/const* 'signed/negative []) value))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- add [left right]
  (app (function/const* 'signed/add []) left right))
(defn- subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'signed/equivalent-transitive [])
       left middle right first second))

(def subtract-add-left-spec
  {:name 'signed/subtract-add-left :universes []
   :type
   (function/forall
    [['prefix signed] ['left signed] ['right signed]]
    (veq (subtract (add 'prefix 'left) (add 'prefix 'right))
         (subtract 'left 'right)))
   :value
   (function/lam
    [['prefix signed] ['left signed] ['right signed]]
    (let [pp (positive 'prefix) np (negative 'prefix)
          pl (positive 'left) nl (negative 'left)
          pr (positive 'right) nr (negative 'right)
          source-positive
          (ring/radd (ring/radd pp pl) (ring/radd np nr))
          source-negative
          (ring/radd (ring/radd np nl) (ring/radd pp pr))
          target-positive (ring/radd pl nr)
          target-negative (ring/radd nl pr)]
      (ring/equiv
       (ring/radd source-positive target-negative)
       (ring/radd target-positive source-negative))))})

(def distance-add-left-spec
  {:name 'signed/distance-add-left :universes []
   :type
   (function/forall
    [['prefix signed] ['left signed] ['right signed]]
    (veq (scalar-distance (add 'prefix 'left)
                          (add 'prefix 'right))
         (scalar-distance 'left 'right)))
   :value
   (function/lam
    [['prefix signed] ['left signed] ['right signed]]
    (app
     (function/const* 'signed/absolute-respects-equivalence [])
     (subtract (add 'prefix 'left) (add 'prefix 'right))
     (subtract 'left 'right)
     (app (function/const* 'signed/subtract-add-left [])
          'prefix 'left 'right)))})

(def distance-add-right-spec
  {:name 'signed/distance-add-right :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['suffix signed]]
    (veq (scalar-distance (add 'left 'suffix)
                          (add 'right 'suffix))
         (scalar-distance 'left 'right)))
   :value
   (function/lam
    [['left signed] ['right signed] ['suffix signed]]
    (let [start
          (scalar-distance (add 'left 'suffix)
                           (add 'right 'suffix))
          commuted
          (scalar-distance (add 'suffix 'left)
                           (add 'suffix 'right))
          finish (scalar-distance 'left 'right)]
      (equivalent-transitive
       start commuted finish
       (app
        (function/const* 'signed/distance-respects-equivalence [])
        (add 'left 'suffix) (add 'suffix 'left)
        (add 'right 'suffix) (add 'suffix 'right)
        (app (function/const* 'signed/add-commutative [])
             'left 'suffix)
        (app (function/const* 'signed/add-commutative [])
             'right 'suffix))
       (app (function/const* 'signed/distance-add-left [])
            'suffix 'left 'right))))})

(def definition-specs [])
(def theorem-specs
  [subtract-add-left-spec
   distance-add-left-spec
   distance-add-right-spec])

(defn extend-environment [env]
  (-> env
      ring/extend-environment
      distance/extend-environment
      (support/extend-with :signed-distance-translation theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
