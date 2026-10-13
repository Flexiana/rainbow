(ns rainbow.math.rational.nnrat.null-scaling
  "Scaling a null sequence by a bounded constant preserves convergence to zero:

    analysis/rate-null-scaled : c <= 1 -> rate-null s M -> rate-null (\\n. c * s n) M

  Composes three earlier results: nnrat/multiply-right-monotone (c <= 1 => c*s n <= 1*s n),
  nnrat/multiply-one-left (1*s n ~ s n), transported by nnrat/at-most-respects-equivalence,
  then rate-null of s.  Lets a geometric/harmonic error bound absorb a bounded prefactor.
  Native and axiom-free; chains nnrat-harmonic-convergence, nnrat-multiply-right-monotone,
  and nnrat-distributive on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.harmonic-convergence :as hc]
            [rainbow.math.rational.nnrat.multiply-right-monotone :as rm]
            [rainbow.math.rational.nnrat.distributive :as dist]))

(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def one (function/const* 'nnrat/one []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def one-nat (succ zero-nat))
(def nnrat-seq (function/arrow nat nnrat))
(def nat-modulus (function/arrow nat nat))

(defn- app [f & args] (apply function/app f args))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- rat-transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))
(defn- at-most-resp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- the-rate-null [s M] (function/app (function/const* 'analysis/rate-null []) s M))

(def rate-null-scaled-spec
  {:name 'analysis/rate-null-scaled :universes []
   :type (function/forall
          [['c nnrat] ['s nnrat-seq] ['M nat-modulus]
           ['hc (rat-at-most 'c one)]
           ['hs (the-rate-null 's 'M)]]
          (the-rate-null (function/lam [['n nat]] (rmul 'c (app 's 'n))) 'M))
   :value
   (function/lam
    [['c nnrat] ['s nnrat-seq] ['M nat-modulus]
     ['hc (rat-at-most 'c one)]
     ['hs (the-rate-null 's 'M)]]
    (function/lam
     [['k nat] ['n nat] ['hn (app (function/const* 'nat/at-most []) (app 'M 'k) 'n)]]
     (let [sn (app 's 'n)
           bound (make one-nat 'k)
           ;; c*sn <= 1*sn
           step1 (function/app (function/const* 'nnrat/multiply-right-monotone [])
                               'c one sn 'hc)
           ;; rewrite 1*sn -> sn : c*sn <= sn
           step2 (at-most-resp (rmul 'c sn) (rmul 'c sn) sn (rmul one sn)
                               (equiv-refl (rmul 'c sn))
                               (equiv-sym (rmul one sn) sn
                                          (function/app (function/const* 'nnrat/multiply-one-left []) sn))
                               step1)]
       ;; c*sn <= sn <= 1/(k+1)
       (rat-transitive (rmul 'c sn) sn bound step2 (app 'hs 'k 'n 'hn)))))})

(def definition-specs [])
(def theorem-specs [rate-null-scaled-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.rational.nnrat.multiply-right-monotone rainbow.math.rational.nnrat.distributive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-null-scaling (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.null-scaling))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
