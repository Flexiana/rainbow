(ns rainbow.math.rational.nnrat.value-iteration
  "The self-contained value-iteration convergence theorem: a contraction recurrence
  drives the error to zero.

    analysis/contraction-converges :
        e 0 <= 1
     -> (forall n, e (n+1) <= (1/2) * e n)         [1/2-contraction recurrence]
     -> rate-null e                                 [e converges to zero]

  This is the frontier-OR payoff on the analysis track: if the value-iteration error
  contracts by 1/2 each sweep (a 1/2-discounted Bellman operator), the iterates provably
  converge.  Proof: induction gives e n <= (1/2)^n (the step uses nnrat/multiply-monotone
  on the recurrence + the bridge equivalence (1/2)*(1/2)^n ~ (1/2)^(n+1), transported by
  at-most-respects-equivalence), then geometric-error-converges (dominated by (1/2)^n ->
  0) closes it.

  The bridge reduces to the nat identity 2*(p+1) = (p+p)+2, proved here via
  multiply-successor-right + multiply-one-right.
  Native and axiom-free; chains nnrat-geometric-convergence and nnrat-multiply-monotone."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.geometric-convergence :as gc]
            [rainbow.math.rational.nnrat.multiply-monotone :as mm]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def one-nat (succ zero-nat))
(def two-nat (succ one-nat))

(defn- app [f & args] (apply function/app f args))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- combine [l r]
  (function/app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- pow2-pred [n] (function/app (function/const* 'nat/pow2-pred []) n))
(defn- geom [n] (function/app (function/const* 'nnrat/geometric-half []) n))
(def half (function/const* 'nnrat/half []))
(defn- rmul [a b] (function/app (function/const* 'nnrat/multiply []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
;; nat equality combinators
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- congruent [mapping l r same]
  (function/app (function/const* 'equality/congruent-function [type-level type-level])
                nat nat mapping l r same))
(defn- mult-one-right [v] (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- mult-succ-right [v f] (function/app (function/const* 'nat/multiply-successor-right []) v f))
(defn- mult-comm [a b] (function/app (function/const* 'nat/multiply-commutative []) a b))
(defn- combine-law [l r] (function/app (function/const* 'nnrat/denominator-combine []) l r))
;; nnrat combinators
(defn- multiply-monotone [c a b h]
  (function/app (function/const* 'nnrat/multiply-monotone []) c a b h))
(defn- rat-transitive [l m r p q]
  (function/app (function/const* 'nnrat/at-most-transitive []) l m r p q))
(defn- at-most-resp [l el r er sl sr ord]
  (function/app (function/const* 'nnrat/at-most-respects-equivalence []) l el r er sl sr ord))
(defn- equiv-sym [l r p] (function/app (function/const* 'nnrat/equivalent-symmetric []) l r p))
(defn- equiv-refl [v] (function/app (function/const* 'nnrat/equivalent-reflexive []) v))
(defn- nat-rec [level motive base step n]
  (function/app (function/const* 'data/Nat.rec [level]) motive base step n))

;; ---- nat: 2*p = p+p ---------------------------------------------------------
(def two-times-spec
  {:name 'nat/two-times :universes []
   :type (function/forall [['p nat]] (eq-nat (nmul two-nat 'p) (nadd 'p 'p)))
   :value (function/lam
           [['p nat]]
           (transitive (nmul two-nat 'p) (nmul 'p two-nat) (nadd 'p 'p)
                       (mult-comm two-nat 'p)                       ; 2*p = p*2
                       (transitive (nmul 'p two-nat) (nadd 'p (nmul 'p one-nat)) (nadd 'p 'p)
                                   (mult-succ-right 'p one-nat)     ; p*(succ 1) = p + p*1
                                   (congruent (function/lam [['v nat]] (nadd 'p 'v))
                                              (nmul 'p one-nat) 'p (mult-one-right 'p)))))})

;; ---- nat: 2*(succ p) = succ(succ(p+p)) --------------------------------------
(def two-times-succ-spec
  {:name 'nat/two-times-succ :universes []
   :type (function/forall [['p nat]]
                          (eq-nat (nmul two-nat (succ 'p)) (succ (succ (nadd 'p 'p)))))
   :value (function/lam
           [['p nat]]
           (transitive (nmul two-nat (succ 'p)) (nadd two-nat (nmul two-nat 'p))
                       (succ (succ (nadd 'p 'p)))
                       (mult-succ-right two-nat 'p)                 ; 2*(succ p) = 2 + 2*p
                       (congruent (function/lam [['v nat]] (nadd two-nat 'v))
                                  (nmul two-nat 'p) (nadd 'p 'p)
                                  (function/app (function/const* 'nat/two-times []) 'p))))})

;; ---- bridge: (1/2) * (1/2)^n ~ (1/2)^(n+1) ----------------------------------
(def geom-halving-spec
  {:name 'nnrat/geometric-half-halving :universes []
   :type (function/forall [['n nat]] (equiv (rmul half (geom 'n)) (geom (succ 'n))))
   :value
   (function/lam
    [['n nat]]
    (let [pp (pow2-pred 'n)
          x (succ (succ (nadd pp pp)))
          ;; equivalent unfolds to: (1*1)*X  =  1*(succ(combine 1 pp))
          lhs (nmul (nmul one-nat one-nat) x)
          rhs (nmul one-nat (succ (combine one-nat pp)))
          m1x (nmul one-nat x)
          c1 (congruent (function/lam [['v nat]] (nmul 'v x))
                        (nmul one-nat one-nat) one-nat (mult-one-right one-nat))  ; lhs = 1*X
          rhs-to-m1x (transitive rhs (nmul one-nat (nmul two-nat (succ pp))) m1x
                                 (congruent (function/lam [['v nat]] (nmul one-nat 'v))
                                            (succ (combine one-nat pp)) (nmul two-nat (succ pp))
                                            (combine-law one-nat pp))              ; rhs = 1*(2*(succ pp))
                                 (congruent (function/lam [['v nat]] (nmul one-nat 'v))
                                            (nmul two-nat (succ pp)) x
                                            (function/app (function/const* 'nat/two-times-succ []) pp)))]
      (transitive lhs m1x rhs c1 (symmetric rhs m1x rhs-to-m1x))))})

;; ---- induction: contraction recurrence => e n <= (1/2)^n --------------------
(def error-below-geometric-spec
  {:name 'analysis/contraction-error-below-geometric :universes []
   :type (function/forall
          [['e (function/arrow nat nnrat)]
           ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
           ['rec (function/forall [['n nat]]
                                  (rat-at-most (app 'e (succ 'n)) (rmul half (app 'e 'n))))]]
          (function/forall [['n nat]] (rat-at-most (app 'e 'n) (geom 'n))))
   :value
   (function/lam
    [['e (function/arrow nat nnrat)]
     ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
     ['rec (function/forall [['n nat]]
                            (rat-at-most (app 'e (succ 'n)) (rmul half (app 'e 'n))))]]
    (function/lam
     [['n nat]]
     (nat-rec [:zero]
             (function/lam [['m nat]] (rat-at-most (app 'e 'm) (geom 'm)))
             'e0
             (function/lam
              [['prev nat] ['ih (rat-at-most (app 'e 'prev) (geom 'prev))]]
              ;; e(succ prev) <= half*e prev <= half*geom prev ~ geom(succ prev)
              (let [step-mul (rat-transitive (app 'e (succ 'prev))
                                             (rmul half (app 'e 'prev))
                                             (rmul half (geom 'prev))
                                             (app 'rec 'prev)
                                             (multiply-monotone half (app 'e 'prev) (geom 'prev) 'ih))]
                (at-most-resp (app 'e (succ 'prev)) (app 'e (succ 'prev))
                              (geom (succ 'prev)) (rmul half (geom 'prev))
                              (equiv-refl (app 'e (succ 'prev)))
                              (equiv-sym (rmul half (geom 'prev)) (geom (succ 'prev))
                                         (function/app (function/const* 'nnrat/geometric-half-halving []) 'prev))
                              step-mul)))
             'n)))})

;; ---- capstone: contraction recurrence => convergence to zero ----------------
(def contraction-converges-spec
  {:name 'analysis/contraction-converges :universes []
   :type (function/forall
          [['e (function/arrow nat nnrat)]
           ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
           ['rec (function/forall [['n nat]]
                                  (rat-at-most (app 'e (succ 'n)) (rmul half (app 'e 'n))))]]
          (function/app (function/const* 'analysis/rate-null [])
                        'e (function/lam [['k nat]] 'k)))
   :value
   (function/lam
    [['e (function/arrow nat nnrat)]
     ['e0 (rat-at-most (app 'e zero-nat) (geom zero-nat))]
     ['rec (function/forall [['n nat]]
                            (rat-at-most (app 'e (succ 'n)) (rmul half (app 'e 'n))))]]
    (function/app (function/const* 'analysis/geometric-error-converges [])
                  'e
                  (function/app (function/const* 'analysis/contraction-error-below-geometric [])
                                'e 'e0 'rec)))})

(def definition-specs [])
(def theorem-specs [two-times-spec two-times-succ-spec geom-halving-spec
                    error-below-geometric-spec contraction-converges-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.geometric-convergence rainbow.math.rational.nnrat.multiply-monotone])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-value-iteration (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.value-iteration))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
