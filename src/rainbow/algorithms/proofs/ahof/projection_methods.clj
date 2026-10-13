(ns rainbow.algorithms.proofs.ahof.projection-methods
  "Kochenderfer constrained/rounded update rules as higher-order-function compositions,
  proved axiom-free, extending the 222 AHoF catalog:

    O10.1 projected gradient descent : project the updated point onto a box [lo,hi]
    D12.3 restricted policy gradient  : clip the update to a trust region [lo,hi]
    O22.2 LP-relaxation-and-round     : round a fractional LP value by a 1/2 threshold

  Both projection/clipping rules are clamp compositions; the feasibility guarantees
  (result lies in [lo,hi]) reuse rainbow.math.logic.clamp-range (clamp-at-most-hi,
  lo-at-most-clamp).  Rounding uses the decidable order + if-data.
  Native and axiom-free; chains clamp-range (-> nnrat-minmax) on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.logic.clamp-range :as cr]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- clamp [r lo hi] (function/app (function/const* 'clamp/clamp []) r lo hi))
(defn- at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(defn- eq-nnrat [l r] (function/equality type-level nnrat l r))
(defn- decide-at-most [a b]
  (function/app (function/const* 'audit/decide-nnrat-at-most []) a b))
(defn- if-data [cond decision then else]
  (function/app (function/const* 'logic/if-data [type-level]) nnrat cond decision then else))
(defn- reflexive-nnrat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nnrat v))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(defn- numeral [n] (nth (iterate succ zero-nat) n))
(defn- rational [n d-pred]
  (function/app (function/const* 'nnrat/make []) (numeral n) (numeral d-pred)))
(def half (rational 1 1))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))

;; ---- O10.1 projected gradient descent ---------------------------------------
(def projected-step-spec
  {:name 'opt/projected-gradient-step :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['x nnrat] ['lo nnrat] ['hi nnrat]] (clamp 'x 'lo 'hi))})

(def projected-below-hi-spec
  {:name 'opt/projected-below-hi :universes []
   :type (function/forall [['x nnrat] ['lo nnrat] ['hi nnrat]]
                          (at-most (function/app (function/const* 'opt/projected-gradient-step [])
                                                 'x 'lo 'hi) 'hi))
   :value (function/lam [['x nnrat] ['lo nnrat] ['hi nnrat]]
                        (function/app (function/const* 'clamp/clamp-at-most-hi []) 'x 'lo 'hi))})

(def projected-above-lo-spec
  {:name 'opt/projected-above-lo :universes []
   :type (function/forall [['x nnrat] ['lo nnrat] ['hi nnrat]
                           ['ordered (at-most 'lo 'hi)]]
                          (at-most 'lo (function/app (function/const* 'opt/projected-gradient-step [])
                                                     'x 'lo 'hi)))
   :value (function/lam [['x nnrat] ['lo nnrat] ['hi nnrat] ['ordered (at-most 'lo 'hi)]]
                        (function/app (function/const* 'clamp/lo-at-most-clamp []) 'x 'lo 'hi 'ordered))})

;; ---- D12.3 restricted (trust-region) policy gradient ------------------------
(def restricted-step-spec
  {:name 'policy/restricted-gradient-step :kind :definition :universes []
   :type (function/arrow nnrat nnrat nnrat nnrat)
   :value (function/lam [['raw nnrat] ['lo nnrat] ['hi nnrat]] (clamp 'raw 'lo 'hi))})

(def restricted-in-trust-hi-spec
  {:name 'policy/restricted-within-trust-hi :universes []
   :type (function/forall [['raw nnrat] ['lo nnrat] ['hi nnrat]]
                          (at-most (function/app (function/const* 'policy/restricted-gradient-step [])
                                                 'raw 'lo 'hi) 'hi))
   :value (function/lam [['raw nnrat] ['lo nnrat] ['hi nnrat]]
                        (function/app (function/const* 'clamp/clamp-at-most-hi []) 'raw 'lo 'hi))})

(def restricted-in-trust-lo-spec
  {:name 'policy/restricted-within-trust-lo :universes []
   :type (function/forall [['raw nnrat] ['lo nnrat] ['hi nnrat]
                           ['ordered (at-most 'lo 'hi)]]
                          (at-most 'lo (function/app (function/const* 'policy/restricted-gradient-step [])
                                                     'raw 'lo 'hi)))
   :value (function/lam [['raw nnrat] ['lo nnrat] ['hi nnrat] ['ordered (at-most 'lo 'hi)]]
                        (function/app (function/const* 'clamp/lo-at-most-clamp []) 'raw 'lo 'hi 'ordered))})

;; ---- O22.2 LP-relaxation-and-round ------------------------------------------
;; round a fractional value: 1 if frac >= 1/2 else 0
(def lp-round-spec
  {:name 'opt/lp-round :kind :definition :universes []
   :type (function/arrow nnrat nnrat)
   :value (function/lam [['frac nnrat]]
                        (if-data (equiv 'frac 'frac) (decide-at-most half 'frac)
                                 nnrat-one nnrat-zero))})

;; frac 3/4 >= 1/2 rounds up to 1
(def lp-round-up-example-spec
  {:name 'opt/lp-round-up-example :universes []
   :type (eq-nnrat (function/app (function/const* 'opt/lp-round []) (rational 3 3)) nnrat-one)
   :value (reflexive-nnrat nnrat-one)})

;; frac 1/4 < 1/2 rounds down to 0
(def lp-round-down-example-spec
  {:name 'opt/lp-round-down-example :universes []
   :type (eq-nnrat (function/app (function/const* 'opt/lp-round []) (rational 1 3)) nnrat-zero)
   :value (reflexive-nnrat nnrat-zero)})

(def definition-specs
  [projected-step-spec restricted-step-spec lp-round-spec])
(def theorem-specs
  [projected-below-hi-spec projected-above-lo-spec
   restricted-in-trust-hi-spec restricted-in-trust-lo-spec
   lp-round-up-example-spec lp-round-down-example-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax rainbow.math.logic.clamp-range])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :ahof-projection-methods (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.ahof.projection-methods))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
