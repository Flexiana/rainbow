(ns rainbow.math.rational.nnrat.convex
  "The convex-combination bound -- the capstone of the nnrat monotonicity + algebra
  foundation:

      convex-at-most-max : (w0 + w1) ~ 1  ->  w0*v0 + w1*v1 <= max v0 v1   (all w0 w1 v0 v1)

  A weighted average with weights summing to one never exceeds the larger value -- the
  universal soundness behind every convex-combination / weighted-average step in the
  AHoF catalog (interpolation, exponential smoothing, mixing, barycentric updates),
  which the catalog exercised only on worked instances.

  Assembly (each piece proved earlier this layer):
    1. wsum2-monotone with max-upper-left/right : w0*v0+w1*v1 <= w0*M + w1*M   (M = max v0 v1)
    2. multiply-distributes-add-right (reversed) : w0*M + w1*M ~ (w0+w1)*M
    3. multiply-respects-equivalence with the hyp : (w0+w1)*M ~ 1*M
    4. multiply-one-left                          : 1*M ~ M
    => w0*M+w1*M ~ M ; transport the bound's right endpoint with
       at-most-respects-equivalence to conclude <= M.

  Native and axiom-free; chains rainbow.math.rational.nnrat.weighted-sum (=> multiply/add
  monotone), rainbow.math.rational.nnrat.minmax, and rainbow.math.rational.nnrat.distributive."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.weighted-sum :as ws]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.nnrat.distributive :as dist]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))

(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- rat-le [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- wsum2 [w0 w1 v0 v1]
  (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))

(defn- app [nm & args] (apply function/app (function/const* nm []) args))

;; proof term of  (w0*P + w1*P) ~ P , given hw : (w0+w1) ~ 1
;; via  sum ~ (w0+w1)*P ~ 1*P ~ P
(defn- scaled-sum-equiv [w0 w1 P hw]
  (let [w-sum (radd w0 w1)
        sum-wp (radd (rmul w0 P) (rmul w1 P))
        distr (app 'nnrat/multiply-distributes-add-right w0 w1 P)      ; (w0+w1)*P ~ sum-wp
        sym-distr (app 'nnrat/equivalent-symmetric (rmul w-sum P) sum-wp distr)
        mreq (app 'nnrat/multiply-respects-equivalence
                  w-sum rone P P hw (app 'nnrat/equivalent-reflexive P)) ; (w0+w1)*P ~ 1*P
        one-p (app 'nnrat/multiply-one-left P)                          ; 1*P ~ P
        t1 (app 'nnrat/equivalent-transitive sum-wp (rmul w-sum P) (rmul rone P)
                sym-distr mreq)]
    (app 'nnrat/equivalent-transitive sum-wp (rmul rone P) P t1 one-p)))  ; sum-wp ~ P

;; (w0+w1)~1 -> w0*v0 + w1*v1 <= max v0 v1
(def convex-at-most-max-spec
  {:name 'nnrat/convex-at-most-max :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
           ['hw (equiv (radd 'w0 'w1) rone)]]
          (rat-le (wsum2 'w0 'w1 'v0 'v1) (rmax 'v0 'v1)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
     ['hw (equiv (radd 'w0 'w1) rone)]]
    (let [M (rmax 'v0 'v1)
          lhs (wsum2 'w0 'w1 'v0 'v1)
          sum-wm (radd (rmul 'w0 M) (rmul 'w1 M))
          ;; wsum2 v0 v1 <= wsum2 M M  (= sum-wm, defeq)
          step1 (app 'nnrat/wsum2-monotone 'w0 'w1 'v0 M 'v1 M
                     (app 'minmax/max-upper-left 'v0 'v1)
                     (app 'minmax/max-upper-right 'v0 'v1))
          sum-wm-eq-M (scaled-sum-equiv 'w0 'w1 M 'hw)         ; sum-wm ~ M
          M-eq-sum-wm (app 'nnrat/equivalent-symmetric sum-wm M sum-wm-eq-M)]
      (app 'nnrat/at-most-respects-equivalence
           lhs lhs M sum-wm (app 'nnrat/equivalent-reflexive lhs) M-eq-sum-wm step1)))})

;; (w0+w1)~1 -> min v0 v1 <= w0*v0 + w1*v1
(def convex-at-least-min-spec
  {:name 'nnrat/convex-at-least-min :universes []
   :type (function/forall
          [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
           ['hw (equiv (radd 'w0 'w1) rone)]]
          (rat-le (rmin 'v0 'v1) (wsum2 'w0 'w1 'v0 'v1)))
   :value
   (function/lam
    [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
     ['hw (equiv (radd 'w0 'w1) rone)]]
    (let [mn (rmin 'v0 'v1)
          lhs (wsum2 'w0 'w1 'v0 'v1)
          sum-wm (radd (rmul 'w0 mn) (rmul 'w1 mn))
          ;; wsum2 mn mn (= sum-wm) <= wsum2 v0 v1
          step1 (app 'nnrat/wsum2-monotone 'w0 'w1 mn 'v0 mn 'v1
                     (app 'minmax/min-lower-left 'v0 'v1)
                     (app 'minmax/min-lower-right 'v0 'v1))
          sum-wm-eq-mn (scaled-sum-equiv 'w0 'w1 mn 'hw)       ; sum-wm ~ mn
          mn-eq-sum-wm (app 'nnrat/equivalent-symmetric sum-wm mn sum-wm-eq-mn)]
      (app 'nnrat/at-most-respects-equivalence
           mn sum-wm lhs lhs mn-eq-sum-wm (app 'nnrat/equivalent-reflexive lhs) step1)))})

(def definition-specs [])
(def theorem-specs [convex-at-most-max-spec convex-at-least-min-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ws/extend-environment
      minmax/extend-environment
      dist/extend-environment
      (support/extend-with :nnrat-convex
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
