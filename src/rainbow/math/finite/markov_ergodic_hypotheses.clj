(ns rainbow.math.finite.markov-ergodic-hypotheses
  "The exact finite-chain hypotheses needed by a future ergodic theorem.

  `markov/nnrat-ergodic-hypotheses` packages row normalization,
  irreducibility, and aperiodicity. It is deliberately named hypotheses: this
  module does not claim convergence, uniqueness, a rate, or a mixing bound.
  For canonical Hastings kernels on Index n, proposal normalization proves row
  normalization, while the executable full-support verdict proves the other
  two fields. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-full-support-irreducible
             :as full-support-cone]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))
(def true-value (function/const* 'data/true []))

(defn- app [f & xs] (apply function/app f xs))
(defn- index-of [upper]
  (app (function/const* 'finite/Index []) upper))
(defn- index-finset [upper]
  (app (function/const* 'finite/index-finset []) upper))
(defn- index-decision [upper]
  (app (function/const* 'finite/index-decide-equality []) upper))
(defn- index-certified [upper]
  (app (function/const* 'finite/index-certified-equality-decision []) upper))
(defn- index-covered [upper]
  (function/lam
   [['state (index-of upper)]]
   (app (function/const* 'finite/index-enumeration-covers []) upper 'state)))
(defn- full-support-decision [element states target proposal]
  (app (function/const* 'mcmc/full-support-decision [zero-level])
       element states target proposal))
(defn- canonical-kernel [element states target proposal decision]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [zero-level])
       element states target proposal decision))
(defn- diagonal-placement [element states target proposal decision]
  (app
   (function/const*
    'mcmc/nnrat-hastings-diagonal-rejection-placement [zero-level])
   element states target proposal decision))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [zero-level])
       element states kernel))
(defn- total-mass [element states mass]
  (app (function/const* 'probability/nnrat-total-mass [zero-level])
       element states mass))
(defn- equivalent [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [zero-level])
       element states kernel mass))
(defn- irreducible [element states decision kernel]
  (app (function/const* 'markov/nnrat-irreducible [zero-level])
       element states decision kernel))
(defn- aperiodic [element states decision kernel]
  (app (function/const* 'markov/nnrat-aperiodic [zero-level])
       element states decision kernel))
(defn- ergodic-hypotheses [element states decision kernel]
  (app (function/const* 'markov/nnrat-ergodic-hypotheses [zero-level])
       element states decision kernel))
(defn- equal-bool [left right]
  (function/equality type-level bool left right))
(defn- conjoin [left right left-proof right-proof]
  (app (function/const* 'proposition/conjoin [])
       left right left-proof right-proof))

(def ergodic-hypotheses-spec
  {:name 'markov/nnrat-ergodic-hypotheses
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S [:sort [:succ [:param 'u]]]]
     ['states
      (app (function/const* 'finset-data/Finset [[:param 'u]]) 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S [:sort [:succ [:param 'u]]]]
     ['states
      (app (function/const* 'finset-data/Finset [[:param 'u]]) 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (proposition/conjunction
     (app (function/const* 'markov/nnrat-kernel-rows-normalized
                           [[:param 'u]])
          'S 'states 'kernel)
     (proposition/conjunction
      (app (function/const* 'markov/nnrat-irreducible [[:param 'u]])
           'S 'states 'decision 'kernel)
      (app (function/const* 'markov/nnrat-aperiodic [[:param 'u]])
           'S 'states 'decision 'kernel))))})

(def index-canonical-kernel-rows-normalized-spec
  {:name 'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]]
    (kernel-normalized
     (index-of 'upper)
     (index-finset 'upper)
     (canonical-kernel
      (index-of 'upper) (index-finset 'upper)
      'target 'proposal (index-decision 'upper))))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          decision (index-decision 'upper)
          placement
          (diagonal-placement element states 'target 'proposal decision)]
      (app
       (function/const*
        'mcmc/nnrat-hastings-completed-kernel-rows-normalized [zero-level])
       element states 'target 'proposal placement
       'proposal-normalized
       (app
        (function/const*
         'mcmc/nnrat-hastings-diagonal-rejection-placement-has-rejection-mass
         [zero-level])
        element states 'target 'proposal decision
        (index-certified 'upper)
        (index-covered 'upper)))))})

(def index-ergodic-hypotheses-spec
  {:name 'mcmc/nnrat-hastings-index-ergodic-hypotheses-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (ergodic-hypotheses
     (index-of 'upper)
     (index-finset 'upper)
     (index-decision 'upper)
     (canonical-kernel
      (index-of 'upper) (index-finset 'upper)
      'target 'proposal (index-decision 'upper))))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          decision (index-decision 'upper)
          kernel (canonical-kernel
                  element states 'target 'proposal decision)
          normalized (kernel-normalized element states kernel)
          irreducible-proof (irreducible element states decision kernel)
          aperiodic-proof (aperiodic element states decision kernel)]
      (conjoin
       normalized
       (proposition/conjunction irreducible-proof aperiodic-proof)
       (app
        (function/const*
         'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized [])
        'upper 'target 'proposal 'proposal-normalized)
       (conjoin
        irreducible-proof aperiodic-proof
        (app
         (function/const*
          'mcmc/nnrat-hastings-index-irreducible-of-full-support [])
         'upper 'target 'proposal 'verdict)
        (app
         (function/const*
          'mcmc/nnrat-hastings-index-aperiodic-of-full-support [])
         'upper 'target 'proposal 'verdict)))))})

(def index-stationary-ergodic-hypotheses-spec
  {:name
   'mcmc/nnrat-hastings-index-stationary-and-ergodic-hypotheses-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['target-normalized
      (equivalent
       (total-mass (index-of 'upper) (index-finset 'upper) 'target)
       nnrat-one)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          decision (index-decision 'upper)
          kernel (canonical-kernel
                  element states 'target 'proposal decision)]
      (proposition/conjunction
       (stationary element states kernel 'target)
       (ergodic-hypotheses element states decision kernel))))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['target-normalized
      (equivalent
       (total-mass (index-of 'upper) (index-finset 'upper) 'target)
       nnrat-one)]
     ['proposal-normalized
      (kernel-normalized
       (index-of 'upper) (index-finset 'upper) 'proposal)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          decision (index-decision 'upper)
          kernel (canonical-kernel
                  element states 'target 'proposal decision)
          stationary-proof (stationary element states kernel 'target)
          hypotheses-proof
          (ergodic-hypotheses element states decision kernel)]
      (conjoin
       stationary-proof hypotheses-proof
       (app
        (function/const*
         'mcmc/nnrat-hastings-index-canonical-kernel-stationary [])
        'upper 'target 'proposal 'target-normalized 'proposal-normalized)
       (app
        (function/const*
         'mcmc/nnrat-hastings-index-ergodic-hypotheses-of-full-support [])
        'upper 'target 'proposal 'proposal-normalized 'verdict))))})

(def definition-specs [ergodic-hypotheses-spec])
(def theorem-specs
  [index-canonical-kernel-rows-normalized-spec
   index-ergodic-hypotheses-spec
   index-stationary-ergodic-hypotheses-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-full-support-irreducible])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-ergodic-hypotheses (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-ergodic-hypotheses))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
