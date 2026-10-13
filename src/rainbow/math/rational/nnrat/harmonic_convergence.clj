(ns rainbow.math.rational.nnrat.harmonic-convergence
  "A CONCRETE convergence theorem: the harmonic sequence 1/(n+1) converges to zero, with
  an explicit modulus.  This is the first fully worked null sequence and it makes the
  convergence toolkit usable.

  Convergence-to-zero is formulated over the positive-rational ladder 1/(k+1) (rather than
  quantifying eps over all nnrat, which would wrongly force eventual-zero):

    analysis/rate-null s M      := forall k n, M k <= n -> s n <= 1/(k+1)
    nnrat/harmonic n            := 1/(n+1)                       (= make 1 n)
    analysis/harmonic-rate-null : rate-null harmonic (identity)  (n >= k => 1/(n+1) <= 1/(k+1))
    analysis/rate-null-dominated: (forall n, t n <= s n) -> rate-null s M -> rate-null t M

  The harmonic bound reduces (nnrat/at-most-from-cross) to 1*(k+1) <= 1*(n+1), i.e.
  nat/multiply-left-monotone applied to succ k <= succ n, which follows from k <= n by a
  witness (proved here as nat/successor-monotone, absent from d63).
  Native and axiom-free; self-contained on d63."
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-seq (function/arrow nat nnrat))
(def nat-modulus (function/arrow nat nat))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def one-nat (succ zero-nat))

(defn- app [f & args] (apply function/app f args))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- harmonic [n] (make one-nat n))
(defn- from-cross [l r ord] (function/app (function/const* 'nnrat/at-most-from-cross []) l r ord))
(defn- mult-left-monotone [factor l r ord]
  (function/app (function/const* 'nat/multiply-left-monotone []) factor l r ord))
(defn- rat-transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- use-witness [pred goal exists handler]
  (function/app (function/const* 'proposition/use-witness [type-level]) nat pred goal exists handler))
(defn- witness [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))
(defn- the-rate-null [s M] (function/app (function/const* 'analysis/rate-null []) s M))

;; nat/successor-monotone : k <= n -> succ k <= succ n   (via witness; absent from d63)
(def successor-monotone-spec
  {:name 'nat/successor-monotone :universes []
   :type (function/forall [['k nat] ['n nat] ['h (nat-at-most 'k 'n)]]
                          (nat-at-most (succ 'k) (succ 'n)))
   :value
   (function/lam
    [['k nat] ['n nat] ['h (nat-at-most 'k 'n)]]
    (use-witness
     (function/lam [['e nat]] (eq-nat (nadd 'k 'e) 'n))
     (nat-at-most (succ 'k) (succ 'n))
     'h
     (function/lam
      [['e nat] ['he (eq-nat (nadd 'k 'e) 'n)]]
      ;; succ k + e = succ (k + e) = succ n
      (witness (function/lam [['d nat]] (eq-nat (nadd (succ 'k) 'd) (succ 'n)))
               'e
               (congruent (function/lam [['m nat]] (succ 'm)) (nadd 'k 'e) 'n 'he)))))})

;; ---- rate-null over the 1/(k+1) ladder --------------------------------------
(def rate-null-spec
  {:name 'analysis/rate-null :kind :definition :universes []
   :type (function/arrow nnrat-seq nat-modulus 'Prop)
   :value (function/lam [['s nnrat-seq] ['M nat-modulus]]
                        (function/forall
                         [['k nat] ['n nat]]
                         (function/arrow (nat-at-most (app 'M 'k) 'n)
                                         (rat-at-most (app 's 'n) (make one-nat 'k)))))})

;; ---- harmonic sequence 1/(n+1) ----------------------------------------------
(def harmonic-spec
  {:name 'nnrat/harmonic :kind :definition :universes []
   :type (function/arrow nat nnrat)
   :value (function/lam [['n nat]] (harmonic 'n))})

;; ---- harmonic converges to zero, modulus = identity -------------------------
(def harmonic-rate-null-spec
  {:name 'analysis/harmonic-rate-null :universes []
   :type (the-rate-null (function/const* 'nnrat/harmonic [])
                        (function/lam [['k nat]] 'k))
   :value
   (function/lam
    [['k nat] ['n nat] ['hkn (nat-at-most 'k 'n)]]
    ;; goal: harmonic n <= 1/(k+1), i.e. make 1 n <= make 1 k
    ;; base cross product: 1*(succ k) <= 1*(succ n)  from  succ k <= succ n
    (from-cross (harmonic 'n) (make one-nat 'k)
                (mult-left-monotone one-nat (succ 'k) (succ 'n)
                                    (function/app (function/const* 'nat/successor-monotone [])
                                                  'k 'n 'hkn))))})

;; ---- comparison test on the ladder ------------------------------------------
(def rate-null-dominated-spec
  {:name 'analysis/rate-null-dominated :universes []
   :type (function/forall
          [['s nnrat-seq] ['t nnrat-seq] ['M nat-modulus]
           ['dom (function/forall [['n nat]] (rat-at-most (app 't 'n) (app 's 'n)))]
           ['hs (the-rate-null 's 'M)]]
          (the-rate-null 't 'M))
   :value
   (function/lam
    [['s nnrat-seq] ['t nnrat-seq] ['M nat-modulus]
     ['dom (function/forall [['n nat]] (rat-at-most (app 't 'n) (app 's 'n)))]
     ['hs (the-rate-null 's 'M)]]
    (function/lam
     [['k nat] ['n nat] ['hn (nat-at-most (app 'M 'k) 'n)]]
     (rat-transitive (app 't 'n) (app 's 'n) (make one-nat 'k)
                     (app 'dom 'n)
                     (app 'hs 'k 'n 'hn))))})

(def definition-specs [rate-null-spec harmonic-spec])
(def theorem-specs [successor-monotone-spec harmonic-rate-null-spec rate-null-dominated-spec])

(defn extend-environment [checked-environment]
  (support/extend-with checked-environment :nnrat-harmonic-convergence
                       (concat definition-specs theorem-specs)))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
