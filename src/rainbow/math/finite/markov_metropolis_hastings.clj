(ns rainbow.math.finite.markov-metropolis-hastings
  "A fully checked finite Metropolis--Hastings independence sampler.

  The worked target on states {0,1} is (1/3,2/3).  Its independence proposal
  equals the target, so the Hastings ratio is one and every proposal is accepted.
  The resulting kernel is the target row at every source.  We prove exact row
  normalization, detailed balance, stationarity, and one-step mixing from every
  normalized initial mass.  Native, kernel-checked, and axiom-free on D63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.markov-cesaro :as cesaro]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def one-nat (function/app (function/const* 'data/succ []) zero-nat))
(def two-nat (function/app (function/const* 'data/succ []) one-nat))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def state-space-type
  (function/app (function/const* 'finset-data/Finset [zero-level]) nat))

(defn- app [f & xs] (apply function/app f xs))
(defn- rational [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- numerator [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- denominator [value]
  (app (function/const* 'nnrat/denominator []) value))
(defn- nat-multiply [left right]
  (app (function/const* 'nat/multiply []) left right))
(defn- closed-equivalence [left right]
  (app (function/const* 'equality/reflexive [type-level])
       nat (nat-multiply (numerator left) (denominator right))))
(def one-third (rational one-nat two-nat))
(def two-thirds (rational two-nat two-nat))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [zero-level])
       element mapping items))
(defn- total-mass [states mass]
  (app (function/const* 'probability/nnrat-total-mass [zero-level])
       nat states mass))
(defn- kernel-step [states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [zero-level])
       nat states kernel mass target))
(defn- kernel-normalized [states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [zero-level])
       nat states kernel))
(defn- detailed-balance [mass kernel]
  (app (function/const* 'markov/nnrat-detailed-balance [zero-level])
       nat mass kernel))
(defn- stationary [states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [zero-level])
       nat states kernel mass))
(defn- state-space [] (function/const* 'mcmc/mh-two-state-space []))
(defn- target-mass
  ([] (function/const* 'mcmc/mh-target-mass []))
  ([state] (app (target-mass) state)))
(defn- proposal
  ([] (function/const* 'mcmc/mh-independence-proposal []))
  ([source target] (app (proposal) source target)))
(defn- acceptance
  ([] (function/const* 'mcmc/mh-acceptance []))
  ([source target] (app (acceptance) source target)))
(defn- mh-kernel
  ([] (function/const* 'mcmc/mh-kernel []))
  ([source target] (app (mh-kernel) source target)))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- multiply-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       left equivalent-left right equivalent-right same-left same-right))

(def mh-two-state-space-spec
  {:name 'mcmc/mh-two-state-space
   :kind :definition
   :universes []
   :transparency :reducible
   :type state-space-type
   :value (app (function/const* 'finset-data/range []) two-nat)})

(def mh-target-mass-spec
  {:name 'mcmc/mh-target-mass
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['state nat]]
    (app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     one-third
     (function/lam
      [['predecessor nat] ['ignored-previous nnrat]]
      (app
       (function/const* 'data/Nat.rec [type-level])
       (function/lam [['ignored nat]] nnrat)
       two-thirds
       (function/lam
        [['ignored-predecessor nat] ['ignored-value nnrat]]
        nnrat-zero)
       'predecessor))
     'state))})

(def mh-independence-proposal-spec
  {:name 'mcmc/mh-independence-proposal
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['ignored-source nat] ['target nat]]
    (target-mass 'target))})

(def mh-acceptance-spec
  {:name 'mcmc/mh-acceptance
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['ignored-source nat] ['ignored-target nat]]
    nnrat-one)})

(def mh-kernel-spec
  {:name 'mcmc/mh-kernel
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nnrat)
   :value
   (function/lam
    [['source nat] ['target nat]]
    (rmul (proposal 'source 'target)
          (acceptance 'source 'target)))})

(def mh-target-normalized-spec
  {:name 'mcmc/mh-target-normalized
   :universes []
   :type (req (total-mass (state-space) (target-mass)) nnrat-one)
   :value
   (closed-equivalence
    (total-mass (state-space) (target-mass)) nnrat-one)})

(def mh-proposal-normalized-spec
  {:name 'mcmc/mh-proposal-normalized
   :universes []
   :type
   (function/forall
    [['source nat]]
    (req (total-mass (state-space) (app (proposal) 'source))
         nnrat-one))
   :value
   (function/lam
    [['source nat]]
    (function/const* 'mcmc/mh-target-normalized []))})

(def mh-all-proposals-accepted-spec
  {:name 'mcmc/mh-all-proposals-accepted
   :universes []
   :type
   (function/forall
    [['source nat] ['target nat]]
    (req (acceptance 'source 'target) nnrat-one))
   :value
   (function/lam
    [['source nat] ['target nat]]
    (equivalent-reflexive nnrat-one))})

(def mh-kernel-equals-proposal-spec
  {:name 'mcmc/mh-kernel-equals-proposal
   :universes []
   :type
   (function/forall
    [['source nat] ['target nat]]
    (req (mh-kernel 'source 'target)
         (proposal 'source 'target)))
   :value
   (function/lam
    [['source nat] ['target nat]]
    (app (function/const* 'nnrat/multiply-one-right [])
         (proposal 'source 'target)))})

(def mh-kernel-rows-normalized-spec
  {:name 'mcmc/mh-kernel-rows-normalized
   :universes []
   :type (kernel-normalized (state-space) (mh-kernel))
   :value
   (function/lam
    [['source nat]]
    (equivalent-transitive
     (total-mass (state-space) (app (mh-kernel) 'source))
     (total-mass (state-space) (app (proposal) 'source))
     nnrat-one
     (app
      (function/const* 'nnrat/map-sum-respects-equivalence [zero-level])
      nat (app (mh-kernel) 'source) (app (proposal) 'source)
      (function/lam
       [['target nat]]
       (app (function/const* 'mcmc/mh-kernel-equals-proposal [])
            'source 'target))
      (app (function/const* 'finset-data/enumeration [zero-level])
           nat (state-space)))
     (app (function/const* 'mcmc/mh-proposal-normalized []) 'source)))})

(def mh-detailed-balance-spec
  {:name 'mcmc/mh-detailed-balance
   :universes []
   :type (detailed-balance (target-mass) (mh-kernel))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (let [left-mass (target-mass 'left)
          right-mass (target-mass 'right)
          left-flow (rmul left-mass (mh-kernel 'left 'right))
          right-flow (rmul right-mass (mh-kernel 'right 'left))
          pure-left (rmul left-mass right-mass)
          pure-right (rmul right-mass left-mass)
          simplify-left
          (multiply-respects
           left-mass left-mass
           (mh-kernel 'left 'right) right-mass
           (equivalent-reflexive left-mass)
           (equivalent-transitive
            (mh-kernel 'left 'right)
            (proposal 'left 'right) right-mass
            (app (function/const* 'mcmc/mh-kernel-equals-proposal [])
                 'left 'right)
            (equivalent-reflexive right-mass)))
          simplify-right
          (multiply-respects
           right-mass right-mass
           (mh-kernel 'right 'left) left-mass
           (equivalent-reflexive right-mass)
           (equivalent-transitive
            (mh-kernel 'right 'left)
            (proposal 'right 'left) left-mass
            (app (function/const* 'mcmc/mh-kernel-equals-proposal [])
                 'right 'left)
            (equivalent-reflexive left-mass)))]
      (equivalent-transitive
       left-flow pure-left right-flow simplify-left
       (equivalent-transitive
        pure-left pure-right right-flow
        (app (function/const* 'nnrat/multiply-commutative [])
             left-mass right-mass)
        (equivalent-symmetric right-flow pure-right simplify-right)))))})

(def mh-target-stationary-spec
  {:name 'mcmc/mh-target-stationary
   :universes []
   :type (stationary (state-space) (mh-kernel) (target-mass))
   :value
   (app
    (function/const* 'markov/nnrat-detailed-balance-implies-stationary
                     [zero-level])
    nat (state-space) (mh-kernel) (target-mass)
    (function/const* 'mcmc/mh-kernel-rows-normalized [])
    (function/const* 'mcmc/mh-detailed-balance []))})

(def mh-mixes-in-one-step-spec
  {:name 'mcmc/mh-mixes-in-one-step
   :universes []
   :type
   (function/forall
    [['initial (function/arrow nat nnrat)]
     ['initial-normalized
      (req (total-mass (state-space) 'initial) nnrat-one)]]
    (function/forall
     [['target nat]]
     (req
      (kernel-step (state-space) (mh-kernel) 'initial 'target)
      (target-mass 'target))))
   :value
   (function/lam
    [['initial (function/arrow nat nnrat)]
     ['initial-normalized
      (req (total-mass (state-space) 'initial) nnrat-one)]]
    (function/lam
     [['target nat]]
     (let [items
           (app (function/const* 'finset-data/enumeration [zero-level])
                nat (state-space))
           target-mass-value (target-mass 'target)
           kernel-flow
           (function/lam
            [['source nat]]
            (rmul (app 'initial 'source)
                  (mh-kernel 'source 'target)))
           target-flow
           (function/lam
            [['source nat]]
            (rmul (app 'initial 'source) target-mass-value))
           replace-kernel
           (app
            (function/const* 'nnrat/map-sum-respects-equivalence [zero-level])
            nat kernel-flow target-flow
            (function/lam
             [['source nat]]
             (multiply-respects
              (app 'initial 'source) (app 'initial 'source)
              (mh-kernel 'source 'target) target-mass-value
              (equivalent-reflexive (app 'initial 'source))
              (equivalent-transitive
               (mh-kernel 'source 'target)
               (proposal 'source 'target) target-mass-value
               (app (function/const* 'mcmc/mh-kernel-equals-proposal [])
                    'source 'target)
               (equivalent-reflexive target-mass-value))))
            items)
           scaled-total
           (rmul (total-mass (state-space) 'initial) target-mass-value)
           factor
           (equivalent-symmetric
            scaled-total
            (map-sum nat target-flow items)
            (app (function/const* 'nnrat/map-sum-scale-right [zero-level])
                 nat 'initial target-mass-value items))
           normalize-product
           (multiply-respects
            (total-mass (state-space) 'initial) nnrat-one
            target-mass-value target-mass-value
            'initial-normalized
            (equivalent-reflexive target-mass-value))
           remove-one
           (app (function/const* 'nnrat/multiply-one-left [])
                target-mass-value)]
       (equivalent-transitive
        (kernel-step (state-space) (mh-kernel) 'initial 'target)
        (map-sum nat target-flow items)
        target-mass-value replace-kernel
        (equivalent-transitive
         (map-sum nat target-flow items)
         scaled-total target-mass-value factor
         (equivalent-transitive
          scaled-total (rmul nnrat-one target-mass-value) target-mass-value
          normalize-product remove-one))))))})

(def definition-specs
  [mh-two-state-space-spec
   mh-target-mass-spec
   mh-independence-proposal-spec
   mh-acceptance-spec
   mh-kernel-spec])

(def theorem-specs
  [mh-target-normalized-spec
   mh-proposal-normalized-spec
   mh-all-proposals-accepted-spec
   mh-kernel-equals-proposal-spec
   mh-kernel-rows-normalized-spec
   mh-detailed-balance-spec
   mh-target-stationary-spec
   mh-mixes-in-one-step-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      cesaro/extend-environment
      (extend-spec-if-missing
       'nnrat/multiply-one-right :nnrat-identities
       identities/multiply-one-right-spec)
      (support/extend-with
       :finite-markov-metropolis-hastings
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
