(ns rainbow.math.rational.nnrat.geometric-convergence
  "The geometric (contraction-rate) convergence payoff, fully self-contained: the
  sequence (1/2)^n converges to zero.  Rather than build nat/power + an Archimedean
  argument, we reach it by DOMINATION from the harmonic sequence:

    nat/pow2-pred n            := 2^n - 1     (defined directly by recursion)
    nat/index-le-pow2-pred     : n <= 2^n - 1 (induction)
    nnrat/geometric-half n     := 1/2^n       (= make 1 (2^n - 1))
    analysis/geometric-below-harmonic : geometric-half n <= 1/(n+1)
    analysis/geometric-half-rate-null : geometric-half -> 0  (rate-null, identity modulus)

  1/2^n <= 1/(n+1) reduces (at-most-from-cross) to succ n <= succ(2^n-1) = 2^n, i.e.
  n <= 2^n - 1; then rate-null-dominated against harmonic-rate-null gives (1/2)^n -> 0.
  This is the (1/2)-contraction convergence rate -- the analytic core of value-iteration
  convergence for a 1/2-discounted Bellman operator.  Native and axiom-free; chains
  rainbow.math.rational.nnrat.harmonic-convergence on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.harmonic-convergence :as hc]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def one-nat (succ zero-nat))

(defn- app [f & args] (apply function/app f args))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- pow2-pred [n] (function/app (function/const* 'nat/pow2-pred []) n))
(defn- geometric [n] (make one-nat (pow2-pred n)))
(defn- nat-at-most-reflexive [v] (function/app (function/const* 'nat/at-most-reflexive []) v))
(defn- nat-transitive [l m r p q]
  (function/app (function/const* 'nat/at-most-transitive []) l m r p q))
(defn- successor-monotone [k n h]
  (function/app (function/const* 'nat/successor-monotone []) k n h))
(defn- from-cross [l r ord] (function/app (function/const* 'nnrat/at-most-from-cross []) l r ord))
(defn- mult-left-monotone [factor l r ord]
  (function/app (function/const* 'nat/multiply-left-monotone []) factor l r ord))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- witness [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))
(defn- nat-rec [level motive base step n]
  (function/app (function/const* 'data/Nat.rec [level]) motive base step n))

;; nat/pow2-pred n = 2^n - 1  (0, 1, 3, 7, ...):  p(0)=0, p(succ k)=succ(p k + p k)
(def pow2-pred-spec
  {:name 'nat/pow2-pred :kind :definition :universes []
   :type (function/arrow nat nat)
   :value (function/lam
           [['n nat]]
           (nat-rec type-level
                    (function/lam [['ignore nat]] nat)
                    zero-nat
                    (function/lam [['prev nat] ['prevval nat]] (succ (nadd 'prevval 'prevval)))
                    'n))})

;; n <= 2^n - 1
(def index-le-pow2-pred-spec
  {:name 'nat/index-le-pow2-pred :universes []
   :type (function/forall [['n nat]] (nat-at-most 'n (pow2-pred 'n)))
   :value (function/lam
           [['n nat]]
           (nat-rec [:zero]
                    (function/lam [['m nat]] (nat-at-most 'm (pow2-pred 'm)))
                    (nat-at-most-reflexive zero-nat)   ; 0 <= pow2-pred 0 (= 0)
                    (function/lam
                     [['prev nat] ['ih (nat-at-most 'prev (pow2-pred 'prev))]]
                     ;; succ prev <= succ(p prev + p prev) = pow2-pred (succ prev)
                     (let [pp (pow2-pred 'prev)
                           a-le-aa (witness (function/lam [['e nat]] (eq-nat (nadd pp 'e) (nadd pp pp)))
                                            pp (reflexive-nat (nadd pp pp)))  ; pp <= pp+pp
                           k-le-aa (nat-transitive 'prev pp (nadd pp pp) 'ih a-le-aa)]
                       (successor-monotone 'prev (nadd pp pp) k-le-aa)))
                    'n))})

;; 1/2^n
(def geometric-spec
  {:name 'nnrat/geometric-half :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['n nat]] (geometric 'n))})

;; 1/2^n <= 1/(n+1)
(def geometric-below-harmonic-spec
  {:name 'analysis/geometric-below-harmonic :universes []
   :type (function/forall [['n nat]]
                          (rat-at-most (function/app (function/const* 'nnrat/geometric-half []) 'n)
                                       (make one-nat 'n)))
   :value (function/lam
           [['n nat]]
           ;; base: 1*(succ n) <= 1*(succ (pow2-pred n))  from  succ n <= succ (pow2-pred n)
           (from-cross (geometric 'n) (make one-nat 'n)
                       (mult-left-monotone one-nat (succ 'n) (succ (pow2-pred 'n))
                                           (successor-monotone 'n (pow2-pred 'n)
                                                               (function/app (function/const* 'nat/index-le-pow2-pred [])
                                                                             'n)))))})

;; (1/2)^n -> 0, by domination from harmonic (identity modulus)
(def geometric-rate-null-spec
  {:name 'analysis/geometric-half-rate-null :universes []
   :type (function/app (function/const* 'analysis/rate-null [])
                       (function/const* 'nnrat/geometric-half [])
                       (function/lam [['k nat]] 'k))
   :value (function/app (function/const* 'analysis/rate-null-dominated [])
                        (function/const* 'nnrat/harmonic [])
                        (function/const* 'nnrat/geometric-half [])
                        (function/lam [['k nat]] 'k)
                        (function/lam [['n nat]]
                                      (function/app (function/const* 'analysis/geometric-below-harmonic []) 'n))
                        (function/const* 'analysis/harmonic-rate-null []))})

;; OR capstone: an error sequence bounded by the (1/2)-geometric rate converges to zero.
;; This is exactly the value-iteration convergence conclusion under the standard
;; geometric error bound  e(n) <= (1/2)^n  (a 1/2-discounted contraction).
(def geometric-error-converges-spec
  {:name 'analysis/geometric-error-converges :universes []
   :type (function/forall
          [['error (function/arrow nat nnrat)]
           ['bound (function/forall [['n nat]]
                                    (rat-at-most (app 'error 'n)
                                                 (function/app (function/const* 'nnrat/geometric-half []) 'n)))]]
          (function/app (function/const* 'analysis/rate-null [])
                        'error (function/lam [['k nat]] 'k)))
   :value (function/lam
           [['error (function/arrow nat nnrat)]
            ['bound (function/forall [['n nat]]
                                     (rat-at-most (app 'error 'n)
                                                  (function/app (function/const* 'nnrat/geometric-half []) 'n)))]]
           (function/app (function/const* 'analysis/rate-null-dominated [])
                         (function/const* 'nnrat/geometric-half [])
                         'error
                         (function/lam [['k nat]] 'k)
                         'bound
                         (function/const* 'analysis/geometric-half-rate-null [])))})

(def definition-specs [pow2-pred-spec geometric-spec])
(def theorem-specs [index-le-pow2-pred-spec geometric-below-harmonic-spec
                    geometric-rate-null-spec geometric-error-converges-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      hc/extend-environment
      (support/extend-with :nnrat-geometric-convergence
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
