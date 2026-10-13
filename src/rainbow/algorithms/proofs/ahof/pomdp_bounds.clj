(ns rainbow.algorithms.proofs.ahof.pomdp-bounds
  "Kochenderfer 'Algorithms for Decision Making' Ch.21 offline POMDP value-function
  bounds, expressed as higher-order-function compositions over belief-weighted
  alpha-vector values and proved axiom-free, extending the 222 AHoF catalog:

    D21.2  QMDP              : value = max_a  sum_s b(s) Q(s,a)   (upper bound)
    D21.3  fast informed bnd : max over observation-corrected action alpha-values
    D21.5  blind lower bound : value of a single fixed action forever (<= QMDP)
    D21.10 sawtooth iteration: belief value <= convex interpolation of corner values

  belief-action-value reuses nnrat/wsum2 (b0*q0 + b1*q1); the max/bounds reuse
  nnrat-minmax; the sawtooth upper bound reuses nnrat/convex-at-most-max.
  Native and axiom-free; chains nnrat-weighted-sum, nnrat-minmax, nnrat-convex on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            ;; convex transitively chains weighted-sum (-> wsum2, multiply/add monotone),
            ;; nnrat-minmax (-> max + bounds) and nnrat-distributive
            [rainbow.math.rational.nnrat.convex :as convex]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))

(defn- wsum2 [w0 w1 v0 v1]
  (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))

(defn- bav [b0 b1 q0 q1]
  (function/app (function/const* 'pomdp/belief-action-value []) b0 b1 q0 q1))

;; belief-weighted action value: sum_s b(s) Q(s,a)  (2-state)
(def belief-action-value-spec
  {:name 'pomdp/belief-action-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['b1 nnrat] ['q0 nnrat] ['q1 nnrat]]
                        (wsum2 'b0 'b1 'q0 'q1))})

;; ---- D21.2 QMDP: max over actions of the belief-action value -----------------
(def qmdp-value-spec
  {:name 'pomdp/qmdp-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                        (rmax (bav 'b0 'b1 'q00 'q10) (bav 'b0 'b1 'q01 'q11)))})

;; QMDP upper-bounds each action's belief value
(def qmdp-dominates-action0-spec
  {:name 'pomdp/qmdp-dominates-action0 :universes []
   :type (function/forall [['b0 nnrat] ['b1 nnrat]
                           ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                          (at-most (bav 'b0 'b1 'q00 'q10)
                                   (function/app (function/const* 'pomdp/qmdp-value [])
                                                 'b0 'b1 'q00 'q10 'q01 'q11)))
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left [])
                                      (bav 'b0 'b1 'q00 'q10) (bav 'b0 'b1 'q01 'q11)))})

(def qmdp-dominates-action1-spec
  {:name 'pomdp/qmdp-dominates-action1 :universes []
   :type (function/forall [['b0 nnrat] ['b1 nnrat]
                           ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                          (at-most (bav 'b0 'b1 'q01 'q11)
                                   (function/app (function/const* 'pomdp/qmdp-value [])
                                                 'b0 'b1 'q00 'q10 'q01 'q11)))
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-right [])
                                      (bav 'b0 'b1 'q00 'q10) (bav 'b0 'b1 'q01 'q11)))})

;; ---- D21.5 blind lower bound: value of one fixed action, provably <= QMDP -----
(def blind-value-spec
  {:name 'pomdp/blind-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['b1 nnrat] ['q0 nnrat] ['q1 nnrat]]
                        (bav 'b0 'b1 'q0 'q1))})

;; the blind (fixed action a0) value never exceeds the QMDP value
(def blind-below-qmdp-spec
  {:name 'pomdp/blind-below-qmdp :universes []
   :type (function/forall [['b0 nnrat] ['b1 nnrat]
                           ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                          (at-most (function/app (function/const* 'pomdp/blind-value [])
                                                 'b0 'b1 'q00 'q10)
                                   (function/app (function/const* 'pomdp/qmdp-value [])
                                                 'b0 'b1 'q00 'q10 'q01 'q11)))
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['q00 nnrat] ['q10 nnrat] ['q01 nnrat] ['q11 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left [])
                                      (bav 'b0 'b1 'q00 'q10) (bav 'b0 'b1 'q01 'q11)))})

;; ---- D21.3 fast informed bound: max over observation-corrected action values --
;; (same alpha-max structure with corrected per-action values; dominance holds)
(def fib-value-spec
  {:name 'pomdp/fib-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['c00 nnrat] ['c10 nnrat] ['c01 nnrat] ['c11 nnrat]]
                        (rmax (bav 'b0 'b1 'c00 'c10) (bav 'b0 'b1 'c01 'c11)))})

(def fib-dominates-action0-spec
  {:name 'pomdp/fib-dominates-action0 :universes []
   :type (function/forall [['b0 nnrat] ['b1 nnrat]
                           ['c00 nnrat] ['c10 nnrat] ['c01 nnrat] ['c11 nnrat]]
                          (at-most (bav 'b0 'b1 'c00 'c10)
                                   (function/app (function/const* 'pomdp/fib-value [])
                                                 'b0 'b1 'c00 'c10 'c01 'c11)))
   :value (function/lam [['b0 nnrat] ['b1 nnrat]
                         ['c00 nnrat] ['c10 nnrat] ['c01 nnrat] ['c11 nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left [])
                                      (bav 'b0 'b1 'c00 'c10) (bav 'b0 'b1 'c01 'c11)))})

;; ---- D21.10 sawtooth: belief value <= convex interpolation of corner values ---
(def sawtooth-interp-spec
  {:name 'pomdp/sawtooth-interp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['c0 nnrat] ['c1 nnrat]]
                        (wsum2 'w0 'w1 'c0 'c1))})

;; the sawtooth interpolation (weights summing to one) never exceeds the larger corner
(def sawtooth-below-max-corner-spec
  {:name 'pomdp/sawtooth-below-max-corner :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['c0 nnrat] ['c1 nnrat]
                           ['hw (equiv (function/app (function/const* 'nnrat/add []) 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'pomdp/sawtooth-interp [])
                                                 'w0 'w1 'c0 'c1)
                                   (rmax 'c0 'c1)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['c0 nnrat] ['c1 nnrat]
                         ['hw (equiv (function/app (function/const* 'nnrat/add []) 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'c0 'c1 'hw))})

(def definition-specs
  [belief-action-value-spec qmdp-value-spec blind-value-spec fib-value-spec
   sawtooth-interp-spec])
(def theorem-specs
  [qmdp-dominates-action0-spec qmdp-dominates-action1-spec
   blind-below-qmdp-spec fib-dominates-action0-spec
   sawtooth-below-max-corner-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-pomdp-bounds (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.pomdp-bounds))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
