(ns rainbow.math.rational.signed.additive-distance
  "Distance bounds from two-sided additive signed inequalities.

  The Bellman contraction interface is naturally stated as

      left <= right + epsilon   and   right <= left + epsilon,

  while residual arguments use `signed/distance`.  This module proves the
  quotient-safe bridge.  Each subtraction inequality is just a rearrangement
  of the corresponding signed-order cross sum, certified by the checked nnrat
  ring normalizer; the existing absolute/deviation characterization then gives
  the distance bound.  Native and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.rational.signed.distance :as distance]))

(def signed (function/const* 'signed/SignedRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- pos [value]
  (app (function/const* 'signed/positive []) value))
(defn- neg [value]
  (app (function/const* 'signed/negative []) value))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- sadd [left right]
  (app (function/const* 'signed/add []) left right))
(defn- negate [value]
  (app (function/const* 'signed/negate []) value))
(defn- subtract [left right]
  (app (function/const* 'signed/subtract []) left right))
(defn- scalar-distance [left right]
  (app (function/const* 'signed/distance []) left right))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- veq [left right]
  (app (function/const* 'signed/equivalent []) left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'signed/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'signed/equivalent-symmetric [])
       left right same))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'signed/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))
(defn- conjoin [left right first second]
  (app (function/const* 'proposition/conjoin [])
       left right first second))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))
(defn- right-conjunct [left right both]
  (app (function/const* 'proposition/right []) left right both))

(def subtract-at-most-of-additive-upper-spec
  {:name 'signed/subtract-at-most-of-additive-upper
   :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['epsilon signed]
     ['upper (sle 'left (sadd 'right 'epsilon))]]
    (sle (subtract 'left 'right) 'epsilon))
   :value
   (function/lam
    [['left signed] ['right signed] ['epsilon signed]
     ['upper (sle 'left (sadd 'right 'epsilon))]]
    (let [pl (pos 'left) nl (neg 'left)
          pr (pos 'right) nr (neg 'right)
          pe (pos 'epsilon) ne (neg 'epsilon)
          goal-left (radd (radd pl nr) ne)
          premise-left (radd pl (radd nr ne))
          goal-right (radd pe (radd nl pr))
          premise-right (radd (radd pr pe) nl)]
      (app (function/const* 'nnrat/at-most-respects-equivalence [])
           goal-left premise-left goal-right premise-right
           (ring/equiv goal-left premise-left)
           (ring/equiv goal-right premise-right)
           'upper)))})

(def distance-at-most-of-additive-closeness-spec
  (let [distance-bound (sle (scalar-distance 'left 'right) 'epsilon)
        forward-bound (sle (subtract 'left 'right) 'epsilon)
        reverse-bound (sle (negate (subtract 'left 'right)) 'epsilon)
        deviations (proposition/conjunction forward-bound reverse-bound)]
    {:name 'signed/distance-at-most-of-additive-closeness
     :universes []
     :type
     (function/forall
      [['left signed] ['right signed] ['epsilon signed]
       ['left-close (sle 'left (sadd 'right 'epsilon))]
       ['right-close (sle 'right (sadd 'left 'epsilon))]]
      distance-bound)
     :value
     (function/lam
      [['left signed] ['right signed] ['epsilon signed]
       ['left-close (sle 'left (sadd 'right 'epsilon))]
       ['right-close (sle 'right (sadd 'left 'epsilon))]]
      (let [forward
            (app
             (function/const*
              'signed/subtract-at-most-of-additive-upper [])
             'left 'right 'epsilon 'left-close)
            reverse-subtract
            (app
             (function/const*
              'signed/subtract-at-most-of-additive-upper [])
             'right 'left 'epsilon 'right-close)
            negated-forward
            (order-respects
             (subtract 'right 'left)
             (negate (subtract 'left 'right))
             'epsilon 'epsilon
             (equivalent-symmetric
              (negate (subtract 'left 'right))
              (subtract 'right 'left)
              (app (function/const* 'signed/negate-subtract [])
                   'left 'right))
             (equivalent-reflexive 'epsilon)
             reverse-subtract)
            characterization
            (app
             (function/const*
              'signed/distance-bounded-iff-deviation-rows [])
             'left 'right 'epsilon)]
        (app (function/const* 'proposition/equivalence-backward [])
             distance-bound deviations characterization
             (conjoin forward-bound reverse-bound
                      forward negated-forward))))}))

(def additive-upper-of-subtract-at-most-spec
  {:name 'signed/additive-upper-of-subtract-at-most
   :universes []
   :type
   (function/forall
    [['left signed] ['right signed] ['epsilon signed]
     ['difference-bound (sle (subtract 'left 'right) 'epsilon)]]
    (sle 'left (sadd 'right 'epsilon)))
   :value
   (function/lam
    [['left signed] ['right signed] ['epsilon signed]
     ['difference-bound (sle (subtract 'left 'right) 'epsilon)]]
    (let [pl (pos 'left) nl (neg 'left)
          pr (pos 'right) nr (neg 'right)
          pe (pos 'epsilon) ne (neg 'epsilon)
          target-left (radd pl (radd nr ne))
          premise-left (radd (radd pl nr) ne)
          target-right (radd (radd pr pe) nl)
          premise-right (radd pe (radd nl pr))]
      (app (function/const* 'nnrat/at-most-respects-equivalence [])
           target-left premise-left target-right premise-right
           (ring/equiv target-left premise-left)
           (ring/equiv target-right premise-right)
           'difference-bound)))})

(def additive-closeness-of-distance-at-most-spec
  (let [distance-bound (sle (scalar-distance 'left 'right) 'epsilon)
        forward-bound (sle (subtract 'left 'right) 'epsilon)
        reverse-bound (sle (negate (subtract 'left 'right)) 'epsilon)
        deviations (proposition/conjunction forward-bound reverse-bound)
        left-close (sle 'left (sadd 'right 'epsilon))
        right-close (sle 'right (sadd 'left 'epsilon))]
    {:name 'signed/additive-closeness-of-distance-at-most
     :universes []
     :type
     (function/forall
      [['left signed] ['right signed] ['epsilon signed]
       ['bounded distance-bound]]
      (proposition/conjunction left-close right-close))
     :value
     (function/lam
      [['left signed] ['right signed] ['epsilon signed]
       ['bounded distance-bound]]
      (let [characterization
            (app
             (function/const*
              'signed/distance-bounded-iff-deviation-rows [])
             'left 'right 'epsilon)
            rows
            (app (function/const* 'proposition/equivalence-forward [])
                 distance-bound deviations characterization 'bounded)
            forward
            (left-conjunct forward-bound reverse-bound rows)
            negated-reverse
            (right-conjunct forward-bound reverse-bound rows)
            reverse
            (order-respects
             (negate (subtract 'left 'right))
             (subtract 'right 'left)
             'epsilon 'epsilon
             (app (function/const* 'signed/negate-subtract [])
                  'left 'right)
             (equivalent-reflexive 'epsilon)
             negated-reverse)]
        (conjoin
         left-close right-close
         (app
          (function/const* 'signed/additive-upper-of-subtract-at-most [])
          'left 'right 'epsilon forward)
         (app
          (function/const* 'signed/additive-upper-of-subtract-at-most [])
          'right 'left 'epsilon reverse))))}))

(def definition-specs [])
(def theorem-specs
  [subtract-at-most-of-additive-upper-spec
   distance-at-most-of-additive-closeness-spec
   additive-upper-of-subtract-at-most-spec
   additive-closeness-of-distance-at-most-spec])

(defn extend-environment [env]
  (-> env
      ring/extend-environment
      distance/extend-environment
      (support/extend-with :signed-additive-distance theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
