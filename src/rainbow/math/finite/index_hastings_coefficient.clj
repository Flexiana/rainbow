(ns rainbow.math.finite.index-hastings-coefficient
  "Explicit proper Dobrushin factors for canonical Hastings on Index(n+1).
  Proposal normalization and the executable full-support verdict discharge
  the coefficient bound. Target normalization is not needed for this bound.
  Proof terms are checked by the focused gate; no sampler correctness claim."
  (:require [rainbow.environment :as environment]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.finite.markov-full-support :as full-support]
            [rainbow.math.finite.markov-ergodic-hypotheses :as hypotheses]
            [rainbow.math.finite.markov-positive-coefficient :as coefficient]
            [rainbow.math.rational.nnrat.unit-fraction :as unit]))

(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [[:zero]]) args))
(def nat (c 'data/Nat))
(def nnrat (c 'nnrat/NonnegativeRational))
(def bool (c 'data/Bool))
(def upper (app 'data/succ 'predecessor))
(def element (app 'finite/Index upper))
(def states (app 'finite/index-finset upper))
(def decision (app 'finite/index-decide-equality upper))
(def anchor (app 'finite/index-last 'predecessor))
(def kernel (poly 'mcmc/nnrat-hastings-canonical-kernel element states 'target 'proposal decision))
(def minimum (poly 'markov/nnrat-kernel-minimum element states kernel anchor anchor))
(def dp (app 'nnrat/denominator-predecessor minimum))
;; Keep the constructor visible in proof statements. Comparing a named
;; factor alias with this constructor would fully normalize the symbolic
;; Hastings kernel under the current conversion checker.
(def factor (unit/proper-complement dp))
(def base-binders [['predecessor nat] ['target (f/arrow element nnrat)]
                   ['proposal (f/arrow element element nnrat)]])

(def factor-spec
  {:name 'mcmc/nnrat-hastings-index-contraction-factor :kind :definition
   :universes [] :transparency :reducible
   :type (f/forall base-binders nnrat)
   :value (f/lam base-binders (unit/proper-complement dp))})

(def factor-proper-spec
  {:name 'mcmc/nnrat-hastings-index-contraction-factor-proper :universes []
   :type (f/forall base-binders
           (app 'nat/at-most (app 'nnrat/numerator factor)
                            (app 'nnrat/denominator-predecessor factor)))
   :value (f/lam base-binders (app 'nnrat/unit-fraction-complement-proper dp))})

(def coefficient-bound-spec
  (let [verdict (f/equality [:succ [:zero]] bool
                  (poly 'mcmc/full-support-decision element states 'target 'proposal)
                  (c 'data/true))
        bindings (into base-binders
                       [['proposal-normalized (poly 'markov/nnrat-kernel-rows-normalized element states 'proposal)]
                        ['full-support verdict]])
        member (fn [i] (poly 'list/membership element
                         (poly 'finset-data/enumeration element states) i))
        anchor-member (app 'finite/index-enumeration-covers upper anchor)]
    {:name 'mcmc/nnrat-hastings-index-dobrushin-bound-of-full-support :universes []
     :type (f/forall bindings
             (app 'signed/at-most
               (poly 'markov/signed-kernel-dobrushin-coefficient element states kernel)
               (app 'signed/from-nnrat factor)))
     :value
     (f/lam bindings
       (poly 'markov/signed-kernel-dobrushin-at-most-of-listed-positive
         element states kernel
         (app 'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized
              upper 'target 'proposal 'proposal-normalized)
         anchor anchor anchor-member anchor-member
         (f/lam [['i element] ['j element] ['i-member (member 'i)] ['j-member (member 'j)]]
           (app 'mcmc/nnrat-hastings-index-canonical-kernel-positive-of-full-support
                upper 'target 'proposal 'full-support 'i 'j))))}))

(def definition-specs [factor-spec])
(def theorem-specs [factor-proper-spec coefficient-bound-spec])
(defn extend-environment [env]
  (let [env (-> env coefficient/extend-environment full-support/extend-environment)
        env (if (environment/resolve-id env 'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized)
              env
              (support/extend-with env :finite-index-hastings-coefficient-support
                [hypotheses/index-canonical-kernel-rows-normalized-spec]))]
    (support/extend-with env :finite-index-hastings-coefficient (concat definition-specs theorem-specs))))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
