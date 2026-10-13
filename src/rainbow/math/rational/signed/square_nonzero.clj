(ns rainbow.math.rational.signed.square-nonzero
  "signed/square-nonzero : not(d ~ 0) -> not(d*d ~ 0). The signed pair unfolds d*d ~ 0 to
  pos(d*d) ~ neg(d*d), i.e. (Pd*Pd + Nd*Nd) ~ (Pd*Nd + Nd*Pd) (modulo add-zero), which is
  exactly nnrat/square-difference-zero's input, giving Pd ~ Nd, i.e. d ~ 0 -- contradicting
  the premise. Core of signed no-zero-divisors for the square case (what strict convexity needs)."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.square-difference-zero :as sdz]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.linear.matrix.action-scale :as action-scale]
            [rainbow.math.rational.signed.strict-order :as strict-order]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence-laws]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nonneg]))

(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- spos [d] (app (function/const* 'signed/positive []) d))
(defn- sneg [d] (app (function/const* 'signed/negative []) d))
(defn- smul [a b] (app (function/const* 'signed/multiply []) a b))
(defn- seqv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- nnadd [a b] (app (function/const* 'nnrat/add []) a b))
(defn- nnequiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- nn-trans [a b c h1 h2] (app (function/const* 'nnrat/equivalent-transitive []) a b c h1 h2))
(defn- nn-sym [a b h] (app (function/const* 'nnrat/equivalent-symmetric []) a b h))
(defn- azr [q] (app (function/const* 'nnrat/add-zero-right []) q))
(defn- azl [q] (app (function/const* 'nnrat/add-zero-left []) q))
(defn- sq-diff-zero [p n h] (app (function/const* 'nnrat/square-difference-zero []) p n h))
(defn- pneg [p] (app (function/const* 'proposition/negation []) p))

(def square-nonzero-spec
  {:name 'signed/square-nonzero
   :universes []
   :type (function/forall [['d signed] ['hd (pneg (seqv 'd szero))]]
                          (pneg (seqv (smul 'd 'd) szero)))
   :value
   (function/lam
    [['d signed] ['hd (pneg (seqv 'd szero))]]
    (function/lam
     [['hdd (seqv (smul 'd 'd) szero)]]
     (let [dd (smul 'd 'd)
           Pdd (spos dd) Ndd (sneg dd)
           Pd (spos 'd) Nd (sneg 'd)
           ;; hdd :defeq nnequiv (Pdd + 0) (0 + Ndd); strip add-zeros -> Pdd ~ Ndd
           pddNdd (nn-trans Pdd (nnadd Pdd nnzero) Ndd
                            (nn-sym (nnadd Pdd nnzero) Pdd (azr Pdd))
                            (nn-trans (nnadd Pdd nnzero) (nnadd nnzero Ndd) Ndd
                                      'hdd (azl Ndd)))
           ;; nnrat/square-difference-zero : (Pd*Pd+Nd*Nd ~ Pd*Nd+Nd*Pd) -> Pd ~ Nd
           ;; Pdd :defeq Pd*Pd+Nd*Nd, Ndd :defeq Pd*Nd+Nd*Pd
           PdNd (sq-diff-zero Pd Nd pddNdd)
           ;; rebuild d ~ 0 :defeq nnequiv (Pd + 0) (0 + Nd)
           d0 (nn-trans (nnadd Pd nnzero) Pd (nnadd nnzero Nd)
                        (azr Pd)
                        (nn-trans Pd Nd (nnadd nnzero Nd) PdNd
                                  (nn-sym (nnadd nnzero Nd) Nd (azl Nd))))]
       (app 'hd d0))))})

(defn- slt [a b] (app (function/const* 'signed/less-than []) a b))
(defn- lt-intro [x y le neq] (app (function/const* 'signed/less-than-intro []) x y le neq))
(defn- zle-nn [x h] (app (function/const* 'signed/zero-at-most-of-nonnegative []) x h))
(defn- square-nn [v] (app (function/const* 'signed/square-nonnegative []) v))
(defn- s-esym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- square-nonzero [d hd] (app (function/const* 'signed/square-nonzero []) d hd))

(def square-positive-spec
  {:name 'signed/square-positive
   :universes []
   :type (function/forall [['d signed] ['hd (pneg (seqv 'd szero))]]
                          (slt szero (smul 'd 'd)))
   :value
   (function/lam
    [['d signed] ['hd (pneg (seqv 'd szero))]]
    (lt-intro szero (smul 'd 'd)
              (zle-nn (smul 'd 'd) (square-nn 'd))                 ; 0 <= d*d
              (function/lam [['h (seqv szero (smul 'd 'd))]]        ; not (0 ~ d*d)
                            (app (square-nonzero 'd 'hd)
                                 (s-esym szero (smul 'd 'd) 'h)))))})

(def theorem-specs [square-nonzero-spec square-positive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.square-difference-zero rainbow.math.rational.nnrat.identities rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.linear.vector.norm-nonnegative])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :signed-square-nonzero theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.square-nonzero))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
