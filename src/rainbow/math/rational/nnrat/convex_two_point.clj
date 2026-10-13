(ns rainbow.math.rational.nnrat.convex-two-point
  "The unnormalized two-point convex-combination bracket over nonnegative rationals:

      (w0+w1)*min(v0,v1) <= w0*v0+w1*v1 <= (w0+w1)*max(v0,v1)

  The weights are arbitrary nonnegative rationals; they need not sum to one.  The
  two bounds are proved separately so each side can be reused directly:

    1. wsum2-monotone lifts min-lower-left/right or max-upper-left/right through
       multiplication by the nonnegative weights and addition;
    2. multiply-distributes-add-right identifies the repeated endpoint sum
       w0*p+w1*p with (w0+w1)*p up to nnrat equivalence;
    3. at-most-respects-equivalence transports the ordered endpoint.

  Native, non-vacuous, and axiom-free; chains rainbow.math.rational.nnrat.weighted-sum,
  rainbow.math.rational.nnrat.minmax, and rainbow.math.rational.nnrat.distributive on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.weighted-sum :as ws]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.nnrat.distributive :as dist]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- wsum2 [w0 w1 v0 v1]
  (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))

(defn- app [nm & args] (apply function/app (function/const* nm []) args))

;; (w0+w1)*min(v0,v1) <= w0*v0+w1*v1
(def two-point-at-least-scaled-min-spec
  {:name 'nnrat/two-point-at-least-scaled-min :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
          (rat-le (rmul (radd 'w0 'w1) (rmin 'v0 'v1))
                  (wsum2 'w0 'w1 'v0 'v1)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
    (let [mn (rmin 'v0 'v1)
          scaled-min (rmul (radd 'w0 'w1) mn)
          sum-min (radd (rmul 'w0 mn) (rmul 'w1 mn))
          weighted (wsum2 'w0 'w1 'v0 'v1)
          lower (app 'nnrat/wsum2-monotone 'w0 'w1 mn 'v0 mn 'v1
                     (app 'minmax/min-lower-left 'v0 'v1)
                     (app 'minmax/min-lower-right 'v0 'v1))
          distributed (app 'nnrat/multiply-distributes-add-right 'w0 'w1 mn)]
      (app 'nnrat/at-most-respects-equivalence
           scaled-min sum-min weighted weighted distributed
           (app 'nnrat/equivalent-reflexive weighted) lower)))})

;; w0*v0+w1*v1 <= (w0+w1)*max(v0,v1)
(def two-point-at-most-scaled-max-spec
  {:name 'nnrat/two-point-at-most-scaled-max :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
          (rat-le (wsum2 'w0 'w1 'v0 'v1)
                  (rmul (radd 'w0 'w1) (rmax 'v0 'v1))))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
    (let [mx (rmax 'v0 'v1)
          weighted (wsum2 'w0 'w1 'v0 'v1)
          scaled-max (rmul (radd 'w0 'w1) mx)
          sum-max (radd (rmul 'w0 mx) (rmul 'w1 mx))
          upper (app 'nnrat/wsum2-monotone 'w0 'w1 'v0 mx 'v1 mx
                     (app 'minmax/max-upper-left 'v0 'v1)
                     (app 'minmax/max-upper-right 'v0 'v1))
          distributed (app 'nnrat/multiply-distributes-add-right 'w0 'w1 mx)]
      (app 'nnrat/at-most-respects-equivalence
           weighted weighted scaled-max sum-max
           (app 'nnrat/equivalent-reflexive weighted) distributed upper)))})

(def definition-specs [])
(def theorem-specs
  [two-point-at-least-scaled-min-spec two-point-at-most-scaled-max-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.weighted-sum rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.distributive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-convex-two-point (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.convex-two-point))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
