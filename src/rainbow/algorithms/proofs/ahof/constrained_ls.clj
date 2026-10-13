(ns rainbow.algorithms.proofs.ahof.constrained-ls
  "Kochenderfer 'Algorithms for Optimization' Ch.11/13 constrained least-squares /
  distributed cores as higher-order-function compositions, proved axiom-free, extending
  the 222 AHoF catalog:

    O13.2 least squares w/ inequalities (LSI) : feasibility test g.x >= h (decidable)
    O13.3 least distance programming (LDP)    : minimum-norm feasible point (min)
    O11.8 consensus ADMM                      : consensus variable = weighted average

  LSI feasibility reuses the decidable order (soundness via decide-at-most-true-sound);
  LDP reuses nnrat-minmax min; the consensus average reuses nnrat/wsum2 and inherits the
  convex bound.  Native and axiom-free; chains nnrat-convex (-> wsum2, minmax) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))
(def bool (function/const* 'data/Bool []))
(def true-value (function/const* 'data/true []))

(defn- wsum2 [w0 w1 v0 v1] (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eq-bool [l r] (function/equality type-level bool l r))
(defn- decide-at-most [a b] (function/app (function/const* 'audit/decide-nnrat-at-most []) a b))

;; ---- O13.2 LSI feasibility test ---------------------------------------------
(def lsi-feasible-spec
  {:name 'opt/lsi-feasible :kind :definition :universes []
   :type (function/arrow nnrat nnrat bool)
   :value (function/lam [['gx nnrat] ['h nnrat]] (decide-at-most 'h 'gx))})

(def lsi-feasible-sound-spec
  {:name 'opt/lsi-feasible-sound :universes []
   :type (function/forall [['gx nnrat] ['h nnrat]
                           ['ok (eq-bool (function/app (function/const* 'opt/lsi-feasible []) 'gx 'h)
                                         true-value)]]
                          (at-most 'h 'gx))
   :value (function/lam [['gx nnrat] ['h nnrat]
                         ['ok (eq-bool (function/app (function/const* 'opt/lsi-feasible []) 'gx 'h)
                                       true-value)]]
                        (function/app (function/const* 'nnrat/decide-at-most-true-sound []) 'h 'gx 'ok))})

;; ---- O13.3 LDP minimum-norm feasible point ----------------------------------
(def ldp-min-norm-spec
  {:name 'opt/ldp-min-norm :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['n0 nnrat] ['n1 nnrat]] (rmin 'n0 'n1))})

(def ldp-below-left-spec
  {:name 'opt/ldp-below-left :universes []
   :type (function/forall [['n0 nnrat] ['n1 nnrat]]
                          (at-most (function/app (function/const* 'opt/ldp-min-norm []) 'n0 'n1) 'n0))
   :value (function/lam [['n0 nnrat] ['n1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-left []) 'n0 'n1))})

(def ldp-below-right-spec
  {:name 'opt/ldp-below-right :universes []
   :type (function/forall [['n0 nnrat] ['n1 nnrat]]
                          (at-most (function/app (function/const* 'opt/ldp-min-norm []) 'n0 'n1) 'n1))
   :value (function/lam [['n0 nnrat] ['n1 nnrat]]
                        (function/app (function/const* 'minmax/min-lower-right []) 'n0 'n1))})

;; ---- O11.8 consensus ADMM: consensus variable = weighted average -------------
(def admm-consensus-spec
  {:name 'opt/admm-consensus :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['x0 nnrat] ['x1 nnrat]]
                        (wsum2 'w0 'w1 'x0 'x1))})

;; the consensus of local copies never exceeds the larger local value
(def admm-consensus-within-max-spec
  {:name 'opt/admm-consensus-within-max :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['x0 nnrat] ['x1 nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'opt/admm-consensus []) 'w0 'w1 'x0 'x1)
                                   (rmax 'x0 'x1)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['x0 nnrat] ['x1 nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'x0 'x1 'hw))})

(def definition-specs [lsi-feasible-spec ldp-min-norm-spec admm-consensus-spec])
(def theorem-specs
  [lsi-feasible-sound-spec ldp-below-left-spec ldp-below-right-spec
   admm-consensus-within-max-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.convex])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-constrained-ls (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.constrained-ls))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
