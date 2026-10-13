(ns rainbow.math.rational.nnrat.inverse-gap-certificate
  "Sharp inverse-gap residual arithmetic directly in NNRAT.

  If rate + gap = 1, inverse * gap = 1, and

      distance <= residual + rate*distance,

  then

      distance <= inverse*residual.

  This is the NNRAT counterpart of the signed affine certificate and is the
  scalar endpoint needed by finite Bellman residual bounds.  Because every
  NNRAT is nonnegative, scaling monotonicity needs no extra sign premise.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-cancellation :as cancellation]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.ring :as ring]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- order-reflexive [value]
  (app (function/const* 'nnrat/at-most-reflexive []) value))
(defn- order-respects [left left-prime right right-prime
                       same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left left-prime right right-prime
       same-left same-right ordered))

(def inverse-gap-residual-bound-spec
  {:name 'nnrat/inverse-gap-residual-bound
   :universes []
   :type
   (function/forall
    [['distance nnrat] ['residual nnrat]
     ['rate nnrat] ['gap nnrat] ['inverse nnrat]
     ['rate-plus-gap-one (req (radd 'rate 'gap) nnrat-one)]
     ['inverse-times-gap-one (req (rmul 'inverse 'gap) nnrat-one)]
     ['self-bound
      (rle 'distance
           (radd 'residual (rmul 'rate 'distance)))]]
    (rle 'distance (rmul 'inverse 'residual)))
   :value
   (function/lam
    [['distance nnrat] ['residual nnrat]
     ['rate nnrat] ['gap nnrat] ['inverse nnrat]
     ['rate-plus-gap-one (req (radd 'rate 'gap) nnrat-one)]
     ['inverse-times-gap-one (req (rmul 'inverse 'gap) nnrat-one)]
     ['self-bound
      (rle 'distance
           (radd 'residual (rmul 'rate 'distance)))]]
    (let [gap-distance (rmul 'gap 'distance)
          rate-distance (rmul 'rate 'distance)
          split (radd gap-distance rate-distance)
          combined (rmul (radd 'gap 'rate) 'distance)
          one-distance (rmul nnrat-one 'distance)
          padded (radd 'residual rate-distance)
          gap-plus-rate-one
          (equivalent-transitive
           (radd 'gap 'rate) (radd 'rate 'gap) nnrat-one
           (app (function/const* 'nnrat/add-commutative [])
                'gap 'rate)
           'rate-plus-gap-one)
          combined-distance
          (equivalent-transitive
           combined one-distance 'distance
           (app
            (function/const*
             'nnrat/multiply-respects-equivalence [])
            (radd 'gap 'rate) nnrat-one
            'distance 'distance
            gap-plus-rate-one
            (equivalent-reflexive 'distance))
           (app (function/const* 'nnrat/multiply-one-left [])
                'distance))
          split-distance
          (equivalent-transitive
           split combined 'distance
           (equivalent-symmetric
            combined split
            (app
             (function/const*
              'nnrat/multiply-distributes-add-right [])
             'gap 'rate 'distance))
           combined-distance)
          split-bound
          (order-respects
           split 'distance padded padded
           split-distance
           (equivalent-reflexive padded)
           'self-bound)
          gap-at-most-residual
          (app (function/const* 'nnrat/at-most-add-right-cancel [])
               gap-distance rate-distance 'residual split-bound)
          scaled-gap (rmul 'inverse gap-distance)
          scaled-residual (rmul 'inverse 'residual)
          scaled-bound
          (app (function/const* 'nnrat/multiply-monotone [])
               'inverse gap-distance 'residual gap-at-most-residual)
          regrouped (rmul (rmul 'inverse 'gap) 'distance)
          scaled-gap-distance
          (equivalent-transitive
           scaled-gap regrouped 'distance
           (equivalent-symmetric
            regrouped scaled-gap
            (app (function/const* 'nnrat/multiply-associative [])
                 'inverse 'gap 'distance))
           (equivalent-transitive
            regrouped one-distance 'distance
            (app
             (function/const*
              'nnrat/multiply-respects-equivalence [])
             (rmul 'inverse 'gap) nnrat-one
             'distance 'distance
             'inverse-times-gap-one
             (equivalent-reflexive 'distance))
            (app (function/const* 'nnrat/multiply-one-left [])
                 'distance)))]
      (order-respects
       'distance scaled-gap scaled-residual scaled-residual
       (equivalent-symmetric
        scaled-gap 'distance scaled-gap-distance)
       (equivalent-reflexive scaled-residual)
       scaled-bound)))})

(def definition-specs [])
(def theorem-specs [inverse-gap-residual-bound-spec])

(defn extend-environment [env]
  (-> env
      cancellation/extend-environment
      multiply-monotone/extend-environment
      ring/extend-environment
      identities/extend-environment
      (support/extend-with :nnrat-inverse-gap-certificate theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
