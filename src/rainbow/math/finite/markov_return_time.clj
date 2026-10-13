(ns rainbow.math.finite.markov-return-time
  "Fixed-horizon return evidence for exact finite Markov kernels.

  `markov/nnrat-return-at` says that iteration from the canonical point mass at
  a state has positive mass back at that same state after the stated natural
  horizon. Every state returns at horizon zero, and a positive self-loop gives
  a return at horizon one. A future period definition must explicitly restrict
  to positive horizons; these facts alone do not claim aperiodicity or mixing.
  Native and axiom-free on D63."
  (:require [rainbow.math.finite.markov-point-mass :as point-mass]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [U])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- point-mass-at [element decision selected state]
  (app (function/const* 'markov/nnrat-point-mass [U])
       element decision selected state))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))
(defn- return-at [element states decision kernel state steps]
  (app (function/const* 'markov/nnrat-return-at [U])
       element states decision kernel state steps))

(def return-at-spec
  {:name 'markov/nnrat-return-at
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S nat 'Prop))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['state 'S]
     ['steps nat]]
    (positive
     (kernel-iterate
      'S 'states 'kernel 'steps
      (function/lam
       [['candidate 'S]]
       (point-mass-at 'S 'decision 'state 'candidate))
      'state)))})

(def return-at-zero-spec
  {:name 'markov/nnrat-return-at-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['state 'S]]
    (return-at 'S 'states 'decision 'kernel 'state zero-nat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['state 'S]]
    (app
     (function/const*
      'markov/nnrat-kernel-iterate-zero-point-mass-positive [U])
     'S 'states 'decision 'kernel 'certified 'state))})

(def return-at-one-of-positive-self-loop-spec
  {:name 'markov/nnrat-return-at-one-of-positive-self-loop
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['state 'S]
     ['self-loop-positive (positive (app 'kernel 'state 'state))]]
    (return-at 'S 'states 'decision 'kernel 'state (succ zero-nat)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['state 'S]
     ['self-loop-positive (positive (app 'kernel 'state 'state))]]
    (app
     (function/const*
      'markov/nnrat-kernel-iterate-one-point-mass-positive [U])
     'S 'states 'decision 'kernel 'exhaustive
     'state 'state 'self-loop-positive))})

(def definition-specs [return-at-spec])
(def theorem-specs
  [return-at-zero-spec return-at-one-of-positive-self-loop-spec])

(defn extend-environment [env]
  (-> env
      point-mass/extend-environment
      (support/extend-with
       :finite-markov-return-time
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
