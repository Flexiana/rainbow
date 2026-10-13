(ns rainbow.math.finite.markov-full-support-irreducible
  "Executable full support certifies irreducibility of finite Index kernels.

  The full-support decision is executable and its soundness theorem supplies
  positivity of every canonical Hastings-kernel entry. Generic finite Markov
  reachability then turns those positive entries into one-step witnesses for
  every ordered state pair. It also supplies a one-step return at every state,
  the concrete positive-horizon prerequisite for a future period theorem. The
  result does not assert aperiodicity, convergence, a spectral gap, or a
  mixing-time bound. Native and axiom-free on D63."
  (:require [rainbow.math.finite.markov-aperiodicity :as aperiodicity]
            [rainbow.math.finite.markov-full-support :as full-support]
            [rainbow.math.finite.markov-reachability :as reachability]
            [rainbow.math.finite.markov-reachability-witness :as witness]
            [rainbow.math.finite.markov-return-time :as return-time]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.divisibility :as divisibility]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- index-of [upper]
  (app (function/const* 'finite/Index []) upper))
(defn- index-finset [upper]
  (app (function/const* 'finite/index-finset []) upper))
(defn- index-decision [upper]
  (app (function/const* 'finite/index-decide-equality []) upper))
(defn- index-exhaustive [upper]
  (app (function/const* 'finite/index-certified-exhaustive-carrier []) upper))
(defn- full-support-decision [element states target proposal]
  (app (function/const* 'mcmc/full-support-decision [zero-level])
       element states target proposal))
(defn- canonical-kernel [element states target proposal decision]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [zero-level])
       element states target proposal decision))
(defn- irreducible [element states decision kernel]
  (app (function/const* 'markov/nnrat-irreducible [zero-level])
       element states decision kernel))
(defn- return-at [element states decision kernel state steps]
  (app (function/const* 'markov/nnrat-return-at [zero-level])
       element states decision kernel state steps))
(defn- aperiodic [element states decision kernel]
  (app (function/const* 'markov/nnrat-aperiodic [zero-level])
       element states decision kernel))
(defn- equal-bool [left right]
  (function/equality type-level bool left right))

(def index-hastings-irreducible-spec
  {:name 'mcmc/nnrat-hastings-index-irreducible-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (irreducible
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
      (app
       (function/const*
        'markov/nnrat-pointwise-positive-implies-irreducible [zero-level])
       element states decision kernel
       (index-exhaustive 'upper)
       (function/lam
        [['source element] ['destination element]]
        (app
         (function/const*
          'mcmc/nnrat-hastings-index-canonical-kernel-positive-of-full-support
         [])
         'upper 'target 'proposal 'verdict 'source 'destination)))))})

(def index-hastings-return-at-one-spec
  {:name 'mcmc/nnrat-hastings-index-return-at-one-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]
     ['state (index-of 'upper)]]
    (return-at
     (index-of 'upper)
     (index-finset 'upper)
     (index-decision 'upper)
     (canonical-kernel
      (index-of 'upper) (index-finset 'upper)
      'target 'proposal (index-decision 'upper))
     'state
     (succ zero-nat)))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]
     ['state (index-of 'upper)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          decision (index-decision 'upper)
          kernel (canonical-kernel
                  element states 'target 'proposal decision)]
      (app
       (function/const*
        'markov/nnrat-return-at-one-of-positive-self-loop [zero-level])
       element states decision kernel
       (index-exhaustive 'upper)
       'state
       (app
        (function/const*
         'mcmc/nnrat-hastings-index-canonical-kernel-positive-of-full-support
         [])
        'upper 'target 'proposal 'verdict 'state 'state))))})

(def index-hastings-aperiodic-spec
  {:name 'mcmc/nnrat-hastings-index-aperiodic-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal
      (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (equal-bool
       (full-support-decision
        (index-of 'upper) (index-finset 'upper) 'target 'proposal)
       true-value)]]
    (aperiodic
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
      (app
       (function/const* 'markov/nnrat-aperiodic-of-all-return-at-one
                        [zero-level])
       element states decision kernel
       (function/lam
        [['state element]]
        (app
         (function/const*
          'mcmc/nnrat-hastings-index-return-at-one-of-full-support [])
         'upper 'target 'proposal 'verdict 'state)))))})

(def definition-specs [])
(def theorem-specs
  [index-hastings-irreducible-spec
   index-hastings-return-at-one-spec
   index-hastings-aperiodic-spec])

(defn extend-environment [env]
  ;; Install full support first, then only the reachability declarations whose
  ;; prerequisites its point-mass cone already supplied. This avoids replaying
  ;; overlapping dependency modules while retaining a standalone proof gate.
  (-> env
      full-support/extend-environment
      (support/extend-with
       :finite-markov-reachability-witness witness/theorem-specs)
      (support/extend-with
       :finite-markov-reachability
       (concat reachability/definition-specs reachability/theorem-specs))
      (support/extend-with
       :finite-markov-return-time
       (concat return-time/definition-specs return-time/theorem-specs))
      divisibility/extend-environment
      (support/extend-with
       :finite-markov-aperiodicity
       (concat aperiodicity/definition-specs aperiodicity/theorem-specs))
      (support/extend-with
       :finite-markov-full-support-irreducible theorem-specs)))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
