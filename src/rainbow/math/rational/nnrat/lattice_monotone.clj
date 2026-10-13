(ns rainbow.math.rational.nnrat.lattice-monotone
  "Universal monotonicity of the exact-rational min and max under the rational order,
  composing the min/max bound + lattice-step theorems from rainbow.math.rational.nnrat.minmax:

      min-monotone : a<=a' -> b<=b' -> min a b <= min a' b'
      max-monotone : a<=a' -> b<=b' -> max a b <= max a' b'

  i.e. improving both arguments never lowers the min or the max.  These upgrade to
  universal the pointwise-dominance behaviour the AHoF catalog exercised on worked
  instances for min/max aggregation (robust worst-case max, bottleneck/min-cost,
  clipping, monitor envelopes).  Each proof lifts the endpoints through
  nnrat/at-most-transitive into the greatest-lower-bound (minmax/at-most-min) or
  least-upper-bound (minmax/at-most-max) step.

  Native and axiom-free; chains rainbow.math.rational.nnrat.minmax (on the d63 base)."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- minimum [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- maximum [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))

;; a<=a' -> b<=b' -> min a b <= min a' b'
(def min-monotone-spec
  {:name 'minmax/min-monotone :universes []
   :type (function/forall
          [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
           ['ha (at-most 'a 'a-hi)] ['hb (at-most 'b 'b-hi)]]
          (at-most (minimum 'a 'b) (minimum 'a-hi 'b-hi)))
   :value
   (function/lam
    [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
     ['ha (at-most 'a 'a-hi)] ['hb (at-most 'b 'b-hi)]]
    (let [m (minimum 'a 'b)
          m-le-a (function/app (function/const* 'minmax/min-lower-left []) 'a 'b)
          m-le-b (function/app (function/const* 'minmax/min-lower-right []) 'a 'b)
          m-le-a-hi (transitive m 'a 'a-hi m-le-a 'ha)
          m-le-b-hi (transitive m 'b 'b-hi m-le-b 'hb)]
      (function/app (function/const* 'minmax/at-most-min [])
                    m 'a-hi 'b-hi m-le-a-hi m-le-b-hi)))})

;; a<=a' -> b<=b' -> max a b <= max a' b'
(def max-monotone-spec
  {:name 'minmax/max-monotone :universes []
   :type (function/forall
          [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
           ['ha (at-most 'a 'a-hi)] ['hb (at-most 'b 'b-hi)]]
          (at-most (maximum 'a 'b) (maximum 'a-hi 'b-hi)))
   :value
   (function/lam
    [['a nnrat] ['a-hi nnrat] ['b nnrat] ['b-hi nnrat]
     ['ha (at-most 'a 'a-hi)] ['hb (at-most 'b 'b-hi)]]
    (let [hi (maximum 'a-hi 'b-hi)
          a-hi-le (function/app (function/const* 'minmax/max-upper-left []) 'a-hi 'b-hi)
          b-hi-le (function/app (function/const* 'minmax/max-upper-right []) 'a-hi 'b-hi)
          a-le-hi (transitive 'a 'a-hi hi 'ha a-hi-le)
          b-le-hi (transitive 'b 'b-hi hi 'hb b-hi-le)]
      (function/app (function/const* 'minmax/at-most-max [])
                    'a 'b hi a-le-hi b-le-hi)))})

(def definition-specs [])
(def theorem-specs [min-monotone-spec max-monotone-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      minmax/extend-environment
      (support/extend-with :nnrat-lattice-monotone
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
