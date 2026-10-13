(ns rainbow.math.finite.markov-expectation-invariance
  "Exact observable invariance under stationary finite Markov dynamics.

  A stationary NNRAT mass gives the same finite expectation before and after
  one kernel step, after every finite iterate, and under every correctly
  normalized finite Cesaro occupation average.  These theorems connect the
  MCMC distribution laws to the reusable finite-expectation interface.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-cesaro :as cesaro]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- expectation [element states mass value]
  (app (function/const* 'probability/nnrat-expectation [U])
       element states mass value))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-iterate [element states kernel steps mass state]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass state))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- cesaro-count [steps]
  (app (function/const* 'markov/nnrat-cesaro-count []) steps))
(defn- cesaro-average [element states kernel steps mass weight state]
  (app (function/const* 'markov/nnrat-cesaro-average [U])
       element states kernel steps mass weight state))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- expectation-respects
  [element states left-mass right-mass left-value right-value
   same-mass same-value]
  (app
   (function/const* 'nnrat/finite-expectation-respects-equivalence [U])
   element states left-mass right-mass left-value right-value
   same-mass same-value))

(def stationary-step-expectation-spec
  {:name 'markov/nnrat-stationary-step-expectation-invariant
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['observable (function/arrow 'S nnrat)]]
    (req
     (expectation
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'state))
      'observable)
     (expectation 'S 'states 'mass 'observable)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['observable (function/arrow 'S nnrat)]]
    (expectation-respects
     'S 'states
     (function/lam
      [['state 'S]]
      (kernel-step 'S 'states 'kernel 'mass 'state))
     'mass 'observable 'observable 'fixed
     (function/lam
      [['state 'S]]
      (equivalent-reflexive (app 'observable 'state)))))})

(def stationary-iterate-expectation-spec
  {:name 'markov/nnrat-stationary-iterate-expectation-invariant
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['observable (function/arrow 'S nnrat)]]
    (req
     (expectation
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state))
      'observable)
     (expectation 'S 'states 'mass 'observable)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['observable (function/arrow 'S nnrat)]]
    (let [iterate-mass
          (function/lam
           [['state 'S]]
           (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state))
          same-mass
          (app
           (function/const* 'markov/nnrat-stationary-kernel-iterate [U])
           'S 'states 'kernel 'mass 'fixed 'steps)]
      (expectation-respects
       'S 'states iterate-mass 'mass 'observable 'observable same-mass
       (function/lam
        [['state 'S]]
        (equivalent-reflexive (app 'observable 'state))))))})

(def stationary-cesaro-expectation-spec
  {:name 'markov/nnrat-stationary-cesaro-expectation-invariant
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]
     ['observable (function/arrow 'S nnrat)]]
    (req
     (expectation
      'S 'states
      (function/lam
       [['state 'S]]
       (cesaro-average
        'S 'states 'kernel 'steps 'mass 'weight 'state))
      'observable)
     (expectation 'S 'states 'mass 'observable)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]
     ['observable (function/arrow 'S nnrat)]]
    (let [average-mass
          (function/lam
           [['state 'S]]
           (cesaro-average
            'S 'states 'kernel 'steps 'mass 'weight 'state))
          same-mass
          (app
           (function/const* 'markov/nnrat-stationary-cesaro-average [U])
           'S 'states 'kernel 'mass 'fixed 'steps 'weight
           'weight-normalized)]
      (expectation-respects
       'S 'states average-mass 'mass 'observable 'observable same-mass
       (function/lam
        [['state 'S]]
        (equivalent-reflexive (app 'observable 'state))))))})

(def definition-specs [])

(def theorem-specs
  [stationary-step-expectation-spec
   stationary-iterate-expectation-spec
   stationary-cesaro-expectation-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-cesaro])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-expectation-invariance theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-expectation-invariance))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
