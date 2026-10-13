(ns rainbow.math.rational.nnrat.convex-normalized
  "The normalized two-point convex bracket over nonnegative rationals.

  Given weights whose total is equivalent to the structurally positive rational
  `s = nnrat/make (data/succ sp) sdp`, the weighted average lies between its
  two inputs:

      min(x,y) <= (w0*x+w1*y)/s <= max(x,y).

  The proofs transport the scaled bounds from nnrat-convex-two-point from the
  coefficient `w0+w1` to `s`, then use the forward directions of the positive
  coefficient normalization equivalences from nnrat-order-scale.  Native,
  non-vacuous, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.convex-two-point :as convex-two-point]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.nnrat.multiply-commute :as multiply-commute]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]
            [rainbow.math.rational.nnrat.order-scale :as scale]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [name & arguments]
  (apply function/app (function/const* name []) arguments))

(defn- succ [value]
  (app 'data/succ value))

(defn- make [numerator denominator-predecessor]
  (app 'nnrat/make numerator denominator-predecessor))

(defn- positive [numerator-predecessor denominator-predecessor]
  (make (succ numerator-predecessor) denominator-predecessor))

(defn- multiply [left right]
  (app 'nnrat/multiply left right))

(defn- add [left right]
  (app 'nnrat/add left right))

(defn- divide [numerator denominator]
  (app 'nnrat/divide numerator denominator))

(defn- at-most [left right]
  (app 'nnrat/at-most left right))

(defn- equivalent [left right]
  (app 'nnrat/equivalent left right))

(defn- minimum [left right]
  (app 'minmax/min left right))

(defn- maximum [left right]
  (app 'minmax/max left right))

(defn- weighted [w0 w1 x y]
  (add (multiply w0 x) (multiply w1 y)))

(defn- equivalent-reflexive [value]
  (app 'nnrat/equivalent-reflexive value))

(defn- equivalent-symmetric [left right same]
  (app 'nnrat/equivalent-symmetric left right same))

(defn- multiply-respects [left equivalent-left right equivalent-right
                          same-left same-right]
  (app 'nnrat/multiply-respects-equivalence
       left equivalent-left right equivalent-right same-left same-right))

(defn- at-most-respects [left equivalent-left right equivalent-right
                         same-left same-right ordered]
  (app 'nnrat/at-most-respects-equivalence
       left equivalent-left right equivalent-right
       same-left same-right ordered))

(defn- equivalence-forward [left right iff evidence]
  (app 'proposition/equivalence-forward left right iff evidence))

;; If w0+w1 is represented by the positive s, then
;; min(x,y) <= (w0*x+w1*y)/s.
(def two-point-normalized-at-least-min-spec
  {:name 'nnrat/two-point-normalized-at-least-min
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat] ['x nnrat] ['y nnrat]
     ['sp nat] ['sdp nat]
     ['total-positive
      (equivalent (add 'w0 'w1) (positive 'sp 'sdp))]]
    (at-most
     (minimum 'x 'y)
     (divide (weighted 'w0 'w1 'x 'y) (positive 'sp 'sdp))))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['x nnrat] ['y nnrat]
     ['sp nat] ['sdp nat]
     ['total-positive
      (equivalent (add 'w0 'w1) (positive 'sp 'sdp))]]
    (let [s (positive 'sp 'sdp)
          total (add 'w0 'w1)
          mn (minimum 'x 'y)
          sum (weighted 'w0 'w1 'x 'y)
          scaled-total (multiply total mn)
          scaled-s (multiply s mn)
          scaled-bound
          (app 'nnrat/two-point-at-least-scaled-min
               'w0 'w1 'x 'y)
          s-equivalent-total
          (equivalent-symmetric total s 'total-positive)
          scaled-s-equivalent-total
          (multiply-respects
           s total mn mn
           s-equivalent-total (equivalent-reflexive mn))
          positive-scaled-bound
          (at-most-respects
           scaled-s scaled-total sum sum
           scaled-s-equivalent-total (equivalent-reflexive sum)
           scaled-bound)
          normalized (at-most mn (divide sum s))
          normalization
          (app 'nnrat/at-most-multiply-left-normalize-upper
               'sp 'sdp mn sum)]
      (equivalence-forward
       (at-most scaled-s sum) normalized normalization
       positive-scaled-bound)))})

;; If w0+w1 is represented by the positive s, then
;; (w0*x+w1*y)/s <= max(x,y).
(def two-point-normalized-at-most-max-spec
  {:name 'nnrat/two-point-normalized-at-most-max
   :universes []
   :type
   (function/forall
    [['w0 nnrat] ['w1 nnrat] ['x nnrat] ['y nnrat]
     ['sp nat] ['sdp nat]
     ['total-positive
      (equivalent (add 'w0 'w1) (positive 'sp 'sdp))]]
    (at-most
     (divide (weighted 'w0 'w1 'x 'y) (positive 'sp 'sdp))
     (maximum 'x 'y)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['x nnrat] ['y nnrat]
     ['sp nat] ['sdp nat]
     ['total-positive
      (equivalent (add 'w0 'w1) (positive 'sp 'sdp))]]
    (let [s (positive 'sp 'sdp)
          total (add 'w0 'w1)
          mx (maximum 'x 'y)
          sum (weighted 'w0 'w1 'x 'y)
          scaled-total (multiply total mx)
          scaled-s (multiply s mx)
          scaled-bound
          (app 'nnrat/two-point-at-most-scaled-max
               'w0 'w1 'x 'y)
          s-equivalent-total
          (equivalent-symmetric total s 'total-positive)
          scaled-s-equivalent-total
          (multiply-respects
           s total mx mx
           s-equivalent-total (equivalent-reflexive mx))
          positive-scaled-bound
          (at-most-respects
           sum sum scaled-s scaled-total
           (equivalent-reflexive sum) scaled-s-equivalent-total
           scaled-bound)
          normalized (at-most (divide sum s) mx)
          normalization
          (app 'nnrat/at-most-multiply-left-normalize-lower
               'sp 'sdp sum mx)]
      (equivalence-forward
       (at-most sum scaled-s) normalized normalization
       positive-scaled-bound)))})

(def definition-specs [])

(def theorem-specs
  [two-point-normalized-at-least-min-spec
   two-point-normalized-at-most-max-spec])

(defn- extend-order-scale-after-convex [checked-environment]
  ;; convex-two-point has already installed multiply-monotone and the
  ;; distributive proof of multiply-one-left.  Install only the remaining
  ;; order-scale prerequisites before its public theorem specs; invoking the
  ;; full scale extender here would try to install the distinct identities
  ;; proof of multiply-one-left under the same alias.
  (-> checked-environment
      order-equivalence/extend-environment
      multiply-commute/extend-environment
      reassociation/extend-environment
      ;; The rate-null law's strict-below toolkit is marker-guarded, so it
      ;; composes here without the duplicate-identity hazard above.
      scale/extend-rate-null-prerequisites
      (support/extend-with :nnrat-order-scale scale/theorem-specs)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex-two-point])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-order-scale-after-convex (support/extend-with :nnrat-convex-normalized theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.convex-normalized))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
