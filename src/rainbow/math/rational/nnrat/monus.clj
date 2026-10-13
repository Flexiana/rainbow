(ns rainbow.math.rational.nnrat.monus
  "Layer 2 of the signed->nnrat magnitude foundation: truncated subtraction on Nnrat.

  nnrat/monus p q -- mirrors nnrat/add but with nat/monus in the numerator (same
  combined denominator). Its num/den reduce definitionally to the cross forms (as
  nnrat/add's do). The cancellation
    nnrat/monus-add-cancel : q <= p  ->  (nnrat/monus p q) + q ~ p
  is what lets a nonnegative signed value's magnitude round-trip through from-nnrat.
  Proof: to-cross gives Bb<=A (nat) with A=num p*den q, Bb=num q*den p; the numerator of
  (monus p q)+q collapses M*dq + Bb*dq = (M+Bb)*dq = A*dq using nat-monus-add-cancel
  (M+Bb=A via the at-most witness) + distributivity; the resulting cross-product equality
  is a pure monomial identity discharged by the nat-ring tactic. Axiom-free; additive."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.nonnegative-rational :as nnrat-core]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equiv]
            [rainbow.math.nat.monus :as natmonus]))

(def ^:private tl [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmonus [a b] (app (function/const* 'nat/monus []) a b))
;; nnrat internals
(defn- pair [num denpred] (app (function/const* 'data/pair [tl tl]) nat nat num denpred))
(defn- numr [x] (app (function/const* 'nnrat/numerator []) x))
(defn- denr [x] (app (function/const* 'nnrat/denominator []) x))
(defn- denpred [x] (app (function/const* 'nnrat/denominator-predecessor []) x))
(defn- combine [l r] (app (function/const* 'nnrat/combine-denominator-predecessors []) l r))
(defn- nnadd [p q] (app (function/const* 'nnrat/add []) p q))
(defn- nnequiv [p q] (app (function/const* 'nnrat/equivalent []) p q))
(defn- nnle [p q] (app (function/const* 'nnrat/at-most []) p q))
(defn- to-cross [p q h] (app (function/const* 'nnrat/at-most-to-cross []) p q h))
;; nat equality helpers
(defn- eqn [x y] (function/equality tl nat x y))
(defn- refl-n [x] (app (function/const* 'equality/reflexive [tl]) nat x))
(defn- sym-n [x y h] (app (function/const* 'equality/symmetric [tl]) nat x y h))
(defn- tr-n [x y z h1 h2] (app (function/const* 'equality/transitive [tl]) nat x y z h1 h2))
(defn- congr-n [ff x y h] (app (function/const* 'equality/congruent-function [tl tl]) nat nat ff x y h))
(defn- mul-add-left [l r f] (app (function/const* 'nat/multiply-add-left []) l r f))  ; (l+r)*f = l*f + r*f
(defn- add-comm-n [l r] (app (function/const* 'nat/add-commutative []) l r))
(defn- monus-cancel [b d] (app (function/const* 'nat/monus-add-cancel-left []) b d))  ; monus(b+d)b = d
(defn- use-witness [pred goal ex handler] (app (function/const* 'proposition/use-witness [tl]) nat pred goal ex handler))
(defn- prod= [a b] (:proof (ring/prove-product-eq a b)))

;; nnrat/monus p q : numerator = nat-monus (num p * den q)(num q * den p), same combined denominator as add.
(def monus-spec
  {:name 'nnrat/monus
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow nnrat nnrat nnrat)
   :value (function/lam [['p nnrat] ['q nnrat]]
                        (pair (nmonus (nmul (numr 'p) (denr 'q)) (nmul (numr 'q) (denr 'p)))
                              (combine (denpred 'p) (denpred 'q))))})
(defn- nnmonus [p q] (app (function/const* 'nnrat/monus []) p q))

;; q <= p  ->  (nnrat/monus p q) + q ~ p
(def monus-add-cancel-spec
  {:name 'nnrat/monus-add-cancel
   :universes []
   :type (function/forall [['p nnrat] ['q nnrat] ['h (nnle 'q 'p)]]
                          (nnequiv (nnadd (nnmonus 'p 'q) 'q) 'p))
   :value
   (function/lam [['p nnrat] ['q nnrat] ['h (nnle 'q 'p)]]
                 (let [np (numr 'p) dp (denr 'p) nq (numr 'q) dq (denr 'q)
                       A (nmul np dq) Bb (nmul nq dp)
                       M (nmonus A Bb)
                       cross (to-cross 'q 'p 'h)                       ; nat-at-most Bb A  (exists d, Bb + d = A)
           ;; M + Bb = A
                       MBbA (use-witness (function/lam [['d nat]] (eqn (nadd Bb 'd) A))
                                         (eqn (nadd M Bb) A)
                                         cross
                                         (function/lam [['d nat] ['hd (eqn (nadd Bb 'd) A)]]
                                                       (let [Meq (tr-n M (nmonus (nadd Bb 'd) Bb) 'd
                                                                       (congr-n (function/lam [['t nat]] (nmonus 't Bb)) A (nadd Bb 'd) (sym-n (nadd Bb 'd) A 'hd))
                                                                       (monus-cancel Bb 'd))]  ; M = d
                                                         (tr-n (nadd M Bb) (nadd 'd Bb) A
                                                               (congr-n (function/lam [['t nat]] (nadd 't Bb)) M 'd Meq)
                                                               (tr-n (nadd 'd Bb) (nadd Bb 'd) A (add-comm-n 'd Bb) 'hd)))))
           ;; numerator of (monus p q)+q collapses to A*dq
                       num-sum (nadd (nmul M dq) (nmul nq (nmul dp dq)))   ; = num((monus p q)+q) defeq
                       numeq (tr-n num-sum (nadd (nmul M dq) (nmul Bb dq)) (nmul A dq)
                                   (congr-n (function/lam [['t nat]] (nadd (nmul M dq) 't)) (nmul nq (nmul dp dq)) (nmul Bb dq) (prod= (nmul nq (nmul dp dq)) (nmul Bb dq)))
                                   (tr-n (nadd (nmul M dq) (nmul Bb dq)) (nmul (nadd M Bb) dq) (nmul A dq)
                                         (sym-n (nmul (nadd M Bb) dq) (nadd (nmul M dq) (nmul Bb dq)) (mul-add-left M Bb dq))
                                         (congr-n (function/lam [['t nat]] (nmul 't dq)) (nadd M Bb) A MBbA)))
           ;; goal cross-product: mul num-sum dp = mul np den-sum, den-sum = (dp*dq)*dq
                       lhs0 (nmul num-sum dp)
                       rhs (nmul np (nmul (nmul dp dq) dq))]
                   (tr-n lhs0 (nmul (nmul A dq) dp) rhs
                         (congr-n (function/lam [['t nat]] (nmul 't dp)) num-sum (nmul A dq) numeq)
                         (prod= (nmul (nmul A dq) dp) rhs))))})

(def theorem-specs [monus-spec monus-add-cancel-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      order-equiv/extend-environment
      natmonus/extend-environment
      (support/extend-with :nnrat-monus theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
