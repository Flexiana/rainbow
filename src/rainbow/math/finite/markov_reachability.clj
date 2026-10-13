(ns rainbow.math.finite.markov-reachability
  "Finite-step reachability and irreducibility for exact finite Markov kernels.

  A target is reachable from a source exactly when some natural-number horizon
  gives positive mass at the target after iterating from the certified point
  mass at the source.  A kernel is irreducible when every ordered state pair is
  reachable.  Reflexivity uses horizon zero; a positive entry uses horizon one;
  positive trajectories give their indexed horizons; and pointwise-positive
  kernels are irreducible.  These are support results, not mixing-time or
  convergence-rate claims.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-point-mass :as point-mass]
            [rainbow.math.finite.markov-reachability-witness :as witness]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

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
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [U])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- point-mass-at [element decision source state]
  (app (function/const* 'markov/nnrat-point-mass [U])
       element decision source state))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))
(defn- reachable [element states decision kernel source target]
  (app (function/const* 'markov/nnrat-reachable [U])
       element states decision kernel source target))
(defn- irreducible [element states decision kernel]
  (app (function/const* 'markov/nnrat-irreducible [U])
       element states decision kernel))
(defn- iterate-positive-evidence
  [element states decision kernel source target]
  (proposition/existence
   type-level nat
   (function/lam
    [['steps nat]]
    (positive
     (kernel-iterate
      element states kernel 'steps
      (function/lam
       [['state element]]
       (point-mass-at element decision source 'state))
      target)))))

(def reachable-spec
  {:name 'markov/nnrat-reachable
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S 'Prop))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['source 'S] ['target 'S]]
    (iterate-positive-evidence
     'S 'states 'decision 'kernel 'source 'target))})

(def irreducible-spec
  {:name 'markov/nnrat-irreducible
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
     [['source 'S] ['target 'S]]
     (reachable
      'S 'states 'decision 'kernel 'source 'target)))})

(def reachable-reflexive-spec
  {:name 'markov/nnrat-reachable-reflexive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['state 'S]]
    (reachable 'S 'states 'decision 'kernel 'state 'state))
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
      'markov/nnrat-point-mass-reflexive-iterate-witness [U])
     'S 'states 'decision 'kernel 'certified 'state))})

(def reachable-of-positive-entry-spec
  {:name 'markov/nnrat-reachable-of-positive-entry
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['source 'S] ['target 'S]
     ['entry-positive (positive (app 'kernel 'source 'target))]]
    (reachable 'S 'states 'decision 'kernel 'source 'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['source 'S] ['target 'S]
     ['entry-positive (positive (app 'kernel 'source 'target))]]
    (app
     (function/const* 'markov/nnrat-positive-entry-iterate-witness [U])
     'S 'states 'decision 'kernel 'exhaustive
     'source 'target 'entry-positive))})

(def reachable-along-positive-trajectory-spec
  (let [trajectory-state (fn [step] (app 'trajectory step))]
    {:name 'markov/nnrat-reachable-along-positive-trajectory
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['decision (function/arrow 'S 'S bool)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['steps nat]]
      (reachable
       'S 'states 'decision 'kernel
       (trajectory-state zero-nat)
       (trajectory-state 'steps)))
     :value
     (function/lam
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['decision (function/arrow 'S 'S bool)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['steps nat]]
      (let [predicate
            (function/lam
             [['horizon nat]]
             (positive
              (kernel-iterate
               'S 'states 'kernel 'horizon
               (function/lam
                [['state 'S]]
                (point-mass-at
                 'S 'decision (trajectory-state zero-nat) 'state))
               (trajectory-state 'steps))))]
        (app
         (function/const* 'proposition/witness [type-level])
         nat predicate 'steps
         (app
          (function/const*
           'markov/nnrat-point-mass-iterate-positive-along-trajectory [U])
          'S 'states 'decision 'kernel 'certified
          'trajectory 'trajectory-member 'edge-positive 'steps))))}))

(def pointwise-positive-implies-irreducible-spec
  {:name 'markov/nnrat-pointwise-positive-implies-irreducible
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['pointwise-positive
      (function/forall
       [['source 'S] ['target 'S]]
       (positive (app 'kernel 'source 'target)))]]
    (irreducible 'S 'states 'decision 'kernel))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['pointwise-positive
      (function/forall
       [['source 'S] ['target 'S]]
       (positive (app 'kernel 'source 'target)))]]
    (function/lam
     [['source 'S] ['target 'S]]
     (app
      (function/const* 'markov/nnrat-reachable-of-positive-entry [U])
      'S 'states 'decision 'kernel 'exhaustive
      'source 'target
      (app 'pointwise-positive 'source 'target))))})

(def definition-specs [reachable-spec irreducible-spec])
(def theorem-specs
  [reachable-reflexive-spec
   reachable-of-positive-entry-spec
   reachable-along-positive-trajectory-spec
   pointwise-positive-implies-irreducible-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-reachability-witness])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-reachability (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-reachability))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
