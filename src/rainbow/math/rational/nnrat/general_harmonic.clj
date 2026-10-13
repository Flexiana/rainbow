(ns rainbow.math.rational.nnrat.general-harmonic
  "General harmonic null sequence, the bound that dominates any contraction rate gamma<1:

    nnrat/general-harmonic ap gp n := a / (a + n*g)   with a = ap+1, g = gp+1
    analysis/general-harmonic-null : rate-null (general-harmonic ap gp) (\\k. a*k)

  a/(a+ng) -> 0: it is <= 1/(k+1) once a*k <= n (modulus M k = a*k), because the
  cross-product a*(k+1) <= a+ng reduces to a*k <= n*g, and a*k <= n <= n*g (g>=1).
  This is the reciprocal form of the Bernoulli bound gamma^n <= a/(a+n(b-a)) written with
  the gap g = b-a, letting arbitrary gamma = a/(a+g) < 1 be handled by domination.
  Native and axiom-free; chains nnrat-harmonic-convergence on d63."
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.rational.nnrat.harmonic-convergence :as hc]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))
(def one-nat (succ zero-nat))

(defn- app [f & args] (apply function/app f args))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- make [num dpred] (function/app (function/const* 'nnrat/make []) num dpred))
(defn- nat-at-most [a b] (function/app (function/const* 'nat/at-most []) a b))
(defn- rat-at-most [a b] (function/app (function/const* 'nnrat/at-most []) a b))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- mult-succ-right [v f] (function/app (function/const* 'nat/multiply-successor-right []) v f))
(defn- mult-one-right [v] (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- mult-comm [a b] (function/app (function/const* 'nat/multiply-commutative []) a b))
(defn- mult-left-monotone [factor l r ord]
  (function/app (function/const* 'nat/multiply-left-monotone []) factor l r ord))
(defn- add-left-monotone [prefix l r ord]
  (function/app (function/const* 'nat/add-left-monotone []) prefix l r ord))
(defn- nat-transitive [l m r p q]
  (function/app (function/const* 'nat/at-most-transitive []) l m r p q))
(defn- successor-monotone [k n h]
  (function/app (function/const* 'nat/successor-monotone []) k n h))
(defn- from-cross [l r ord] (function/app (function/const* 'nnrat/at-most-from-cross []) l r ord))
(defn- rewrite-left [left replacement right same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-left []) left replacement right same ordered))
(defn- rewrite-right [left right replacement same ordered]
  (function/app (function/const* 'nat/at-most-rewrite-right []) left right replacement same ordered))
(defn- witness [pred val proof]
  (function/app (function/const* 'proposition/witness [type-level]) nat pred val proof))

;; general-harmonic ap gp n = (ap+1) / ((ap+1) + n*(gp+1))
(def general-harmonic-spec
  {:name 'nnrat/general-harmonic :kind :definition :universes []
   :type (function/arrow nat nat nat nnrat)
   :value (function/lam [['ap nat] ['gp nat] ['n nat]]
                        (make (succ 'ap) (nadd 'ap (nmul 'n (succ 'gp)))))})

(def general-harmonic-null-spec
  {:name 'analysis/general-harmonic-null :universes []
   :type (function/forall
          [['ap nat] ['gp nat]]
          (function/app (function/const* 'analysis/rate-null [])
                        (function/app (function/const* 'nnrat/general-harmonic []) 'ap 'gp)
                        (function/lam [['k nat]] (nmul (succ 'ap) 'k))))
   :value
   (function/lam
    [['ap nat] ['gp nat]]
    (let [a (succ 'ap) g (succ 'gp)]
      (function/lam
       [['k nat] ['n nat] ['hn (nat-at-most (nmul a 'k) 'n)]]
       (let [ng (nmul 'n g)
             y (nadd a ng)                       ; a + n*g  (= denominator of the bound)
             bnd (make one-nat 'k)
             ;; one <= g  (= succ gp)
             one-le-g (successor-monotone zero-nat 'gp
                                          (witness (function/lam [['e nat]] (eq-nat (nadd zero-nat 'e) 'gp))
                                                   'gp (reflexive-nat 'gp)))
             ;; n <= n*g   (n*1 <= n*g, and n*1 = n)
             n-le-ng (rewrite-left 'n (nmul 'n one-nat) ng
                                   (symmetric (nmul 'n one-nat) 'n (mult-one-right 'n))
                                   (mult-left-monotone 'n one-nat g one-le-g))
             ;; a*k <= n*g
             ak-le-ng (nat-transitive (nmul a 'k) 'n ng 'hn n-le-ng)
             ;; a + a*k <= a + n*g
             core (add-left-monotone a (nmul a 'k) ng ak-le-ng)
             ;; base: a*(succ k) <= 1*(a + n*g)
             e1 (mult-succ-right a 'k)            ; a*(succ k) = a + a*k
             step-l (rewrite-left (nmul a (succ 'k)) (nadd a (nmul a 'k)) y e1 core)
             ;; 1*y = y  (commute + one-right)
             e2 (transitive (nmul one-nat y) (nmul y one-nat) y (mult-comm one-nat y) (mult-one-right y))
             step-r (rewrite-right (nmul a (succ 'k)) y (nmul one-nat y)
                                   (symmetric (nmul one-nat y) y e2) step-l)]
         ;; base(general-harmonic ap gp n)(1/(k+1)) holds -> lift with from-cross
         (from-cross (make a (nadd 'ap ng)) bnd step-r)))))})

(def definition-specs [general-harmonic-spec])
(def theorem-specs [general-harmonic-null-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.harmonic-convergence])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-general-harmonic (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.general-harmonic))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
