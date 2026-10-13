(ns rainbow.math.finite.markov-aperiodicity
  "Aperiodicity from exact finite-state return horizons.

  A state is aperiodic when every natural divisor common to all of its positive
  return horizons also divides one. This is the gcd-one definition expressed
  without adding a gcd operator to the trusted language. A kernel is aperiodic
  when every state is. A return at horizon one discharges the common-divisor
  condition directly. No convergence rate or mixing theorem is claimed.
  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-return-time :as return-time]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.divisibility :as divisibility]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def one-nat (function/app (function/const* 'data/succ []) zero-nat))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- divides [divisor value]
  (app (function/const* 'nat/divides []) divisor value))
(defn- return-at [element states decision kernel state steps]
  (app (function/const* 'markov/nnrat-return-at [U])
       element states decision kernel state steps))
(defn- aperiodic-at [element states decision kernel state]
  (app (function/const* 'markov/nnrat-aperiodic-at [U])
       element states decision kernel state))
(defn- aperiodic [element states decision kernel]
  (app (function/const* 'markov/nnrat-aperiodic [U])
       element states decision kernel))

(def aperiodic-at-spec
  {:name 'markov/nnrat-aperiodic-at
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'Prop))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['state 'S]]
    (function/forall
     [['divisor nat]]
     (function/arrow
      (function/forall
       [['predecessor nat]]
       (function/arrow
        (return-at
         'S 'states 'decision 'kernel 'state (succ 'predecessor))
        (divides 'divisor (succ 'predecessor))))
      (divides 'divisor one-nat))))})

(def aperiodic-spec
  {:name 'markov/nnrat-aperiodic
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['state 'S]]
     (aperiodic-at 'S 'states 'decision 'kernel 'state)))})

(def aperiodic-at-of-return-at-one-spec
  {:name 'markov/nnrat-aperiodic-at-of-return-at-one
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['state 'S]
     ['returns-at-one
      (return-at 'S 'states 'decision 'kernel 'state one-nat)]]
    (aperiodic-at 'S 'states 'decision 'kernel 'state))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['state 'S]
     ['returns-at-one
      (return-at 'S 'states 'decision 'kernel 'state one-nat)]
     ['divisor nat]
     ['common-divisor
      (function/forall
       [['predecessor nat]]
       (function/arrow
        (return-at
         'S 'states 'decision 'kernel 'state (succ 'predecessor))
        (divides 'divisor (succ 'predecessor))))]]
    (app 'common-divisor zero-nat 'returns-at-one))})

(def aperiodic-of-all-return-at-one-spec
  {:name 'markov/nnrat-aperiodic-of-all-return-at-one
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['all-return-at-one
      (function/forall
       [['state 'S]]
       (return-at 'S 'states 'decision 'kernel 'state one-nat))]]
    (aperiodic 'S 'states 'decision 'kernel))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['all-return-at-one
      (function/forall
       [['state 'S]]
       (return-at 'S 'states 'decision 'kernel 'state one-nat))]
     ['state 'S]]
    (app
     (function/const* 'markov/nnrat-aperiodic-at-of-return-at-one [U])
     'S 'states 'decision 'kernel 'state
     (app 'all-return-at-one 'state)))})

(def definition-specs [aperiodic-at-spec aperiodic-spec])
(def theorem-specs
  [aperiodic-at-of-return-at-one-spec
   aperiodic-of-all-return-at-one-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-return-time rainbow.math.nat.divisibility])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-aperiodicity (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-aperiodicity))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
