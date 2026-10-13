(ns rainbow.math.nat.monus
  "Truncated subtraction on Nat (monus), the missing arithmetic primitive under the
  signed->nnrat magnitude foundation.

    nat/monus 0 b            = 0
    nat/monus (succ a) 0     = succ a
    nat/monus (succ a)(succ b) = nat/monus a b      (double recursion, like decide-at-most)

  Plus the cancellation law needed to extract a magnitude:
    nat/monus-add-cancel-left : nat/monus (b + d) b = d
  (every step is the double-recursion's definitional succ/succ collapse plus the IH,
  since algebra/nat-add recurses on its LEFT argument). Axiom-free; additive."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nat-rec [motive zc sc t] (app (function/const* 'data/Nat.rec [type-level]) motive zc sc t))
(defn- nat-rec-prop [motive zc sc t] (app (function/const* 'data/Nat.rec [[:zero]]) motive zc sc t))
(defn- eq-nat [x y] (function/equality type-level nat x y))
(defn- refl-nat [x] (app (function/const* 'equality/reflexive [type-level]) nat x))

(def ^:private arrow-nn (function/arrow nat nat))

;; nat/monus : Nat -> Nat -> Nat, by recursion on the first arg returning Nat -> Nat.
(def monus-spec
  {:name 'nat/monus
   :kind :definition
   :transparency :reducible
   :universes []
   :type (function/arrow nat nat nat)
   :value
   (function/lam [['a nat] ['b nat]]
                 (app
                  (nat-rec (function/lam [['x nat]] arrow-nn)
                           (function/lam [['b nat]] zero)                       ; monus 0 b = 0
                           (function/lam [['a2 nat] ['ih arrow-nn]]             ; a = succ a2 ; ih = monus a2
                                         (function/lam [['b nat]]
                                                       (nat-rec (function/lam [['x nat]] nat)
                                                                (succ 'a2)                        ; monus (succ a2) 0 = succ a2
                                                                (function/lam [['b2 nat] ['ihb nat]] (app 'ih 'b2))  ; monus (succ a2)(succ b2) = monus a2 b2
                                                                'b)))
                           'a)
                  'b))})
(defn- monus [a b] (app (function/const* 'nat/monus []) a b))

;; nat/monus-zero-right : monus a 0 = a  (per-case reflexivity; needed because monus
;; recurses on its FIRST arg, so monus a 0 is stuck for a variable a).
(def monus-zero-right-spec
  {:name 'nat/monus-zero-right
   :universes []
   :type (function/forall [['a nat]] (eq-nat (monus 'a zero) 'a))
   :value
   (function/lam [['a nat]]
                 (nat-rec-prop (function/lam [['a nat]] (eq-nat (monus 'a zero) 'a))
                               (refl-nat zero)
                               (function/lam [['a2 nat] ['ih (eq-nat (monus 'a2 zero) 'a2)]] (refl-nat (succ 'a2)))
                               'a))})
(defn- mzr [a] (app (function/const* 'nat/monus-zero-right []) a))

;; nat/monus-add-cancel-left : monus (b + d) b = d, by induction on b.
(def monus-add-cancel-left-spec
  {:name 'nat/monus-add-cancel-left
   :universes []
   :type (function/forall [['b nat] ['d nat]] (eq-nat (monus (nadd 'b 'd) 'b) 'd))
   :value
   (function/lam [['b nat]]
                 (nat-rec-prop (function/lam [['b nat]] (function/forall [['d nat]] (eq-nat (monus (nadd 'b 'd) 'b) 'd)))
              ;; b = 0 : monus (0 + d) 0 = monus d 0 = d   (defeq)
                               (function/lam [['d nat]] (mzr 'd))
              ;; b = succ b2 : monus ((succ b2)+d)(succ b2) = monus (b2 + d) b2 = IH d   (defeq collapse + IH)
                               (function/lam [['b2 nat] ['ih (function/forall [['d nat]] (eq-nat (monus (nadd 'b2 'd) 'b2) 'd))]]
                                             (function/lam [['d nat]] (app 'ih 'd)))
                               'b))})

(def theorem-specs [monus-spec monus-zero-right-spec monus-add-cancel-left-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (support/extend-with checked-environment :nat-monus theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.monus))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
