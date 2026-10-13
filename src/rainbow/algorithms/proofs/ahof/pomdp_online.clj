(ns rainbow.algorithms.proofs.ahof.pomdp-online
  "Kochenderfer 'Algorithms for Decision Making' Ch.21-23 online / point-based / controller
  POMDP cores as higher-order-function compositions, proved axiom-free (each with its most
  distinctive structural property), extending the 222 AHoF catalog:

    D21.8  Perseus (randomized PBVI)  : backup keeps the better alpha -> value never decreases
    D22.3  DESPOT (anytime search)    : maintains a lower<=upper value bracket
    D21.16 Freudenthal grid VI        : barycentric interpolation, bounded by the corners
    D23.3  controller policy iteration : finite-state-controller node = expected successor value

  Reuses nnrat-minmax (monotone backup, bracket via transitivity) and nnrat/wsum2 +
  convex-at-most-max (interpolation / expectation).
  Native and axiom-free; chains nnrat-convex on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.convex :as convex]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def rone (function/const* 'nnrat/one []))

(defn- wsum2 [w0 w1 v0 v1] (function/app (function/const* 'nnrat/wsum2 []) w0 w1 v0 v1))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- rmax [a b] (function/app (function/const* 'minmax/max []) a b))
(defn- rmin [a b] (function/app (function/const* 'minmax/min []) a b))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(def ^:private nat (function/const* 'data/Nat []))
(defn- num [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- den [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- equiv-cross [x lit]
  (function/app (function/const* 'equality/reflexive [type-level]) nat (nmul (num x) (den lit))))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- numeral [n] (nth (iterate succ zero-nat) n))
(defn- rational [n d-pred] (function/app (function/const* 'nnrat/make []) (numeral n) (numeral d-pred)))
(def half (rational 1 1))

;; ---- D21.8 Perseus: randomized PBVI backup keeps the better value ------------
(def perseus-backup-spec
  {:name 'pomdp/perseus-backup :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['old nnrat] ['candidate nnrat]] (rmax 'old 'candidate))})

(def perseus-improves-spec
  {:name 'pomdp/perseus-improves :universes []
   :type (function/forall [['old nnrat] ['candidate nnrat]]
                          (at-most 'old (function/app (function/const* 'pomdp/perseus-backup []) 'old 'candidate)))
   :value (function/lam [['old nnrat] ['candidate nnrat]]
                        (function/app (function/const* 'minmax/max-upper-left []) 'old 'candidate))})

;; ---- D22.3 DESPOT: anytime lower<=upper value bracket ------------------------
(def despot-lower-spec
  {:name 'pomdp/despot-lower :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['l nnrat] ['u nnrat]] (rmin 'l 'u))})

(def despot-upper-spec
  {:name 'pomdp/despot-upper :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['l nnrat] ['u nnrat]] (rmax 'l 'u))})

(def despot-bracket-spec
  {:name 'pomdp/despot-bracket :universes []
   :type (function/forall [['l nnrat] ['u nnrat]]
                          (at-most (function/app (function/const* 'pomdp/despot-lower []) 'l 'u)
                                   (function/app (function/const* 'pomdp/despot-upper []) 'l 'u)))
   :value (function/lam [['l nnrat] ['u nnrat]]
                        (function/app (function/const* 'nnrat/at-most-transitive [])
                                      (rmin 'l 'u) 'u (rmax 'l 'u)
                                      (function/app (function/const* 'minmax/min-lower-right []) 'l 'u)
                                      (function/app (function/const* 'minmax/max-upper-right []) 'l 'u)))})

;; ---- D21.16 Freudenthal grid VI: barycentric interpolation ------------------
(def freudenthal-interp-spec
  {:name 'pomdp/freudenthal-interp :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]]
                        (wsum2 'w0 'w1 'v0 'v1))})

(def freudenthal-within-corners-spec
  {:name 'pomdp/freudenthal-within-corners :universes []
   :type (function/forall [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
                           ['hw (equiv (radd 'w0 'w1) rone)]]
                          (at-most (function/app (function/const* 'pomdp/freudenthal-interp []) 'w0 'w1 'v0 'v1)
                                   (rmax 'v0 'v1)))
   :value (function/lam [['w0 nnrat] ['w1 nnrat] ['v0 nnrat] ['v1 nnrat]
                         ['hw (equiv (radd 'w0 'w1) rone)]]
                        (function/app (function/const* 'nnrat/convex-at-most-max [])
                                      'w0 'w1 'v0 'v1 'hw))})

;; ---- D23.3 controller policy iteration: FSC node expected value --------------
(def controller-node-value-spec
  {:name 'pomdp/controller-node-value :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat nnrat)
   :value (function/lam [['p0 nnrat] ['p1 nnrat] ['v0 nnrat] ['v1 nnrat]]
                        (wsum2 'p0 'p1 'v0 'v1))})

;; worked: successor distribution (1/2,1/2) over node values (1,0) -> node value 1/2
(def controller-node-value-example-spec
  {:name 'pomdp/controller-node-value-example :universes []
   :type (equiv (function/app (function/const* 'pomdp/controller-node-value []) half half rone (rational 0 0))
                (rational 1 1))
   :value (equiv-cross (function/app (function/const* 'pomdp/controller-node-value []) half half rone (rational 0 0))
                       (rational 1 1))})

(def definition-specs
  [perseus-backup-spec despot-lower-spec despot-upper-spec freudenthal-interp-spec
   controller-node-value-spec])
(def theorem-specs
  [perseus-improves-spec despot-bracket-spec freudenthal-within-corners-spec
   controller-node-value-example-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      convex/extend-environment
      (support/extend-with :ahof-pomdp-online
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
