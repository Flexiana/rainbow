(ns rainbow.math.finite.markov-reachability-witness
  "Existential finite-horizon witnesses for exact-rational Markov support.

  This module deliberately does not choose a public reachability predicate.
  It packages the two canonical evidence constructors that such an API needs:
  zero steps witness reflexive support of a point mass, and one step witnesses
  support whenever the corresponding kernel entry is positive.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-point-mass :as point-mass]
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

(def positive-entry-iterate-witness-spec
  {:name 'markov/nnrat-positive-entry-iterate-witness
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
    (iterate-positive-evidence
     'S 'states 'decision 'kernel 'source 'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['source 'S] ['target 'S]
     ['entry-positive (positive (app 'kernel 'source 'target))]]
    (let [predicate
          (function/lam
           [['steps nat]]
           (positive
            (kernel-iterate
             'S 'states 'kernel 'steps
             (function/lam
              [['state 'S]]
              (point-mass-at 'S 'decision 'source 'state))
             'target)))]
      (app
       (function/const* 'proposition/witness [type-level])
       nat predicate (succ zero-nat)
       (app
        (function/const*
         'markov/nnrat-kernel-iterate-one-point-mass-positive [U])
        'S 'states 'decision 'kernel 'exhaustive
        'source 'target 'entry-positive))))})

(def point-mass-reflexive-iterate-witness-spec
  {:name 'markov/nnrat-point-mass-reflexive-iterate-witness
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['source 'S]]
    (iterate-positive-evidence
     'S 'states 'decision 'kernel 'source 'source))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['source 'S]]
    (let [predicate
          (function/lam
           [['steps nat]]
           (positive
            (kernel-iterate
             'S 'states 'kernel 'steps
             (function/lam
              [['state 'S]]
              (point-mass-at 'S 'decision 'source 'state))
             'source)))]
      (app
       (function/const* 'proposition/witness [type-level])
       nat predicate zero-nat
       (app
        (function/const*
         'markov/nnrat-kernel-iterate-zero-point-mass-positive [U])
        'S 'states 'decision 'kernel 'certified 'source))))})

(def definition-specs [])
(def theorem-specs
  [positive-entry-iterate-witness-spec
   point-mass-reflexive-iterate-witness-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-point-mass])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-reachability-witness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-reachability-witness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
