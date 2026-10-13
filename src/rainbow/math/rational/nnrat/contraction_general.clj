(ns rainbow.math.rational.nnrat.contraction-general
  "Generalized contraction convergence: ANY contraction rate gamma <= 1/2 drives the
  error to zero.

    analysis/contraction-converges-general :
        gamma <= 1/2
     -> e 0 <= 1
     -> (forall n, e (n+1) <= gamma * e n)
     -> rate-null e

  Reduces to the 1/2 theorem by factor comparison: from gamma <= 1/2,
  nnrat/multiply-right-monotone gives gamma * e n <= (1/2) * e n, so the gamma-recurrence
  implies the 1/2-recurrence, and analysis/contraction-converges closes it.  Covers the
  whole strong-contraction regime (rates up to 1/2).
  Native and axiom-free; chains nnrat-value-iteration and nnrat-multiply-right-monotone."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.value-iteration :as vi]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as rm]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def half (function/const* 'nnrat/half []))

(defn- app [f & args] (apply function/app f args))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- geom [n] (function/app (function/const* 'nnrat/geometric-half []) n))
(defn- rat-transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))

(def contraction-converges-general-spec
  {:name 'analysis/contraction-converges-general :universes []
   :type (function/forall
          [['gamma nnrat] ['e (function/arrow nat nnrat)]
           ['hgamma (rat-at-most 'gamma half)]
           ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
           ['rec (function/forall [['n nat]]
                                  (rat-at-most (app 'e (succ 'n)) (rmul 'gamma (app 'e 'n))))]]
          (function/app (function/const* 'analysis/rate-null [])
                        'e (function/lam [['k nat]] 'k)))
   :value
   (function/lam
    [['gamma nnrat] ['e (function/arrow nat nnrat)]
     ['hgamma (rat-at-most 'gamma half)]
     ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
     ['rec (function/forall [['n nat]]
                            (rat-at-most (app 'e (succ 'n)) (rmul 'gamma (app 'e 'n))))]]
    ;; derive the 1/2-recurrence: e(n+1) <= gamma*e n <= (1/2)*e n
    (let [rec-half
          (function/lam
           [['n nat]]
           (rat-transitive (app 'e (succ 'n)) (rmul 'gamma (app 'e 'n)) (rmul half (app 'e 'n))
                           (app 'rec 'n)
                           (function/app (function/const* 'nnrat/multiply-right-monotone [])
                                         'gamma half (app 'e 'n) 'hgamma)))]
      (function/app (function/const* 'analysis/contraction-converges [])
                    'e 'e0 rec-half)))})

(def definition-specs [])
(def theorem-specs [contraction-converges-general-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.value-iteration rainbow.math.rational.nnrat.multiply-right-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-contraction-general (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.contraction-general))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
