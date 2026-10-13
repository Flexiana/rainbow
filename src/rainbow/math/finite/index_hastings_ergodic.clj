(ns rainbow.math.finite.index-hastings-ergodic
  "The finite ergodic theorem, instantiated for canonical Hastings kernels.

  For the canonical Metropolis-Hastings kernel on Index(n+1) built from a
  target and a normalized proposal, the executable full-support verdict
  alone certifies the Dobrushin factor d/(d+1) (d the kernel minimum's
  denominator predecessor), and both halves of the abstract theorem pair
  instantiate: any two equal-total-mass stationary distributions agree
  pointwise on the carrier, and iterates of any equal-mass start approach
  a stationary distribution inside the explicit (d/(d+1))^n envelope.

  Scope, carried from the design notes: the factor is a
  CERTIFIED rate, not THE rate -- conservative and dependent on the
  kernel's raw representation -- and nothing here is a mixing-time,
  spectral-gap, or sampling statement. The factor stays constructor-
  visible (make d d) throughout; naming it behind an alias makes the
  conversion checker normalize the symbolic kernel. Native and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.index-hastings-coefficient :as index-coefficient]
            [rainbow.math.finite.markov-contraction-uniqueness :as conditional]
            [rainbow.math.finite.markov-coupling-coefficient :as coupling-coefficient]
            [rainbow.math.finite.markov-coupling-distance :as coupling-distance]
            [rainbow.math.finite.markov-dobrushin-contraction :as contraction]
            [rainbow.math.finite.markov-dobrushin-statement :as statement]
            [rainbow.math.finite.markov-ergodic-uniqueness :as uniqueness]
            [rainbow.math.finite.markov-geometric-convergence :as geometric]
            [rainbow.math.finite.markov-geometric-decay :as decay]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.finite.markov-kernel-composition :as composition]
            [rainbow.math.finite.markov-stationary-iterate :as fixed]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.fubini :as fubini]
            [rainbow.math.rational.nnrat.power :as power]
            [rainbow.math.rational.nnrat.order-scale :as scale]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]
            [rainbow.math.rational.nnrat.weighted-map-sum-distance :as weighted]
            [rainbow.math.rational.signed.geometric-bridge :as embedding]))

(def zero-level [:zero])
(def type-level [:succ [:zero]])
(defn- c [name] (f/const* name []))
(defn- app [name & args] (apply f/app (c name) args))
(defn- poly [name & args] (apply f/app (f/const* name [zero-level]) args))
(def nat (c 'data/Nat))
(def nnrat (c 'nnrat/NonnegativeRational))
(def bool (c 'data/Bool))

;; The Index(n+1) world, mirroring finite_index_hastings_coefficient.clj
;; builder for builder so every term is syntactically shared.
(def upper (app 'data/succ 'predecessor))
(def element (app 'finite/Index upper))
(def states (app 'finite/index-finset upper))
(def decision (app 'finite/index-decide-equality upper))
(def kernel
  (poly 'mcmc/nnrat-hastings-canonical-kernel
        element states 'target 'proposal decision))
(def anchor (app 'finite/index-last 'predecessor))
(def minimum
  (poly 'markov/nnrat-kernel-minimum element states kernel anchor anchor))
(def dp (app 'nnrat/denominator-predecessor minimum))
(def factor (app 'nnrat/make dp dp))

(defn- mass-type [] (f/arrow element nnrat))
(defn- req [a b] (app 'nnrat/equivalent a b))
(defn- rle [a b] (app 'nnrat/at-most a b))
(defn- rmul [a b] (app 'nnrat/multiply a b))
(defn- total [mass] (poly 'probability/nnrat-total-mass element states mass))
(defn- stationary [mass]
  (poly 'markov/nnrat-stationary element states kernel mass))
(defn- tv [a b] (poly 'markov/nnrat-total-variation element states a b))
(defn- iterate-mass [steps mass]
  (poly 'markov/nnrat-kernel-iterate element states kernel steps mass))
(defn- rpow [base steps] (app 'nnrat/power base steps))
(defn- membership [value]
  (poly 'list/membership element
        (poly 'finset-data/enumeration element states) value))
(defn- verdict []
  (f/equality type-level bool
              (poly 'mcmc/full-support-decision element states 'target 'proposal)
              (c 'data/true)))

(def shared-binders
  [['predecessor nat] ['target (mass-type)]
   ['proposal (f/arrow element element nnrat)]
   ['proposal-normalized
    (poly 'markov/nnrat-kernel-rows-normalized element states 'proposal)]
   ['full-support (verdict)]])

(defn- normalized-term []
  (app 'mcmc/nnrat-hastings-index-canonical-kernel-rows-normalized
       upper 'target 'proposal 'proposal-normalized))
(defn- coefficient-bound-term []
  (app 'mcmc/nnrat-hastings-index-dobrushin-bound-of-full-support
       'predecessor 'target 'proposal 'proposal-normalized 'full-support))
(defn- proper-term []
  ;; nat/at-most-reflexive at dp is SYNTACTICALLY the capstone's proper
  ;; slot (np = dp = the same term), so no conversion happens. Using the
  ;; index module's factor-proper here instead makes the checker compare
  ;; numerator(make d d) against d, and on that mismatch the current
  ;; conversion checker fully normalizes the symbolic Hastings kernel
  ;; inside d -- the exact budget blow-up the coefficient analysis warned
  ;; about.
  (app 'nat/at-most-reflexive dp))

(def hastings-stationary-unique-spec
  (let [bindings (into shared-binders
                       [['left (mass-type)] ['right (mass-type)]
                        ['left-stationary (stationary 'left)]
                        ['right-stationary (stationary 'right)]
                        ['equal-total-mass (req (total 'left) (total 'right))]
                        ['state element]
                        ['member (membership 'state)]])]
    {:name 'mcmc/nnrat-hastings-index-stationary-unique-of-full-support
     :universes []
     :type (f/forall bindings (req (f/app 'left 'state) (f/app 'right 'state)))
     :value
     (f/lam bindings
            (poly 'markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound
                  element states kernel dp dp
                  (proper-term)
                  (normalized-term)
                  (coefficient-bound-term)
                  'left 'right 'left-stationary 'right-stationary
                  'equal-total-mass 'state 'member))}))

(def hastings-geometric-convergence-spec
  (let [bindings (into shared-binders
                       [['start (mass-type)] ['pi (mass-type)]
                        ['pi-stationary (stationary 'pi)]
                        ['equal-total-mass (req (total 'start) (total 'pi))]
                        ['steps nat]])]
    {:name 'mcmc/nnrat-hastings-index-geometric-convergence-of-full-support
     :universes []
     :type
     (f/forall bindings
               (rle (tv (iterate-mass 'steps 'start) 'pi)
                    (rmul (rpow factor 'steps) (tv 'start 'pi))))
     :value
     (f/lam bindings
            (poly 'markov/nnrat-kernel-iterate-geometric-convergence-to-stationary
                  element states kernel factor
                  (normalized-term)
                  (coefficient-bound-term)
                  'start 'pi 'pi-stationary 'equal-total-mass 'steps))}))

(def definition-specs [])
(def theorem-specs [hastings-stationary-unique-spec
                    hastings-geometric-convergence-spec])

(defn- guard [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn- guard-extend [env marker extend]
  (if (environment/resolve-id env marker) env (extend env)))

;; Their index-coefficient world enters whole (self-consistent on
;; D63 by its own gate); everything from this side enters per-spec,
;; guarded, so shared sub-worlds are never re-installed.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.index-hastings-coefficient])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (guard-extend 'signed/from-nnrat-at-most-reverse (fn [e] (support/add-spec e :finite-index-hastings-ergodic-support embedding/from-nnrat-at-most-reverse-spec))) (guard 'nnrat/weighted-map-sum-distance-bound :nnrat-weighted-map-sum-distance weighted/spec) (guard 'nnrat/map-sum-swap :nnrat-fubini fubini/map-sum-swap-spec) (guard 'markov/nnrat-kernel-step-coupling-distance-bound :finite-markov-coupling-distance coupling-distance/coupling-distance-bound-spec) (guard 'markov/nnrat-kernel-step-positive-residual-coupling-bound :finite-markov-coupling-distance coupling-distance/positive-residual-coupling-bound-spec) (guard 'markov/nnrat-positive-residual-coupling-total :finite-markov-coupling-distance coupling-distance/residual-coupling-total-spec) (guard 'markov/nnrat-row-l1-at-most-twice-dobrushin-bound :finite-markov-coupling-coefficient coupling-coefficient/row-l1-at-most-twice-rho-spec) (guard 'markov/nnrat-coupling-row-cost-at-most-dobrushin-bound :finite-markov-coupling-coefficient coupling-coefficient/coupling-cost-at-most-spec) (guard 'markov/nnrat-kernel-step-positive-residual-contraction :finite-markov-coupling-coefficient coupling-coefficient/positive-residual-contraction-spec) (guard 'markov/nnrat-dobrushin-contraction-estimate :finite-markov-dobrushin-statement statement/contraction-statement-spec) (guard 'markov/nnrat-kernel-step-preserves-total-mass-equivalence :finite-markov-kernel-composition composition/kernel-step-preserves-total-mass-spec) (guard 'markov/nnrat-kernel-step-zero-residual-contraction :finite-markov-dobrushin-contraction contraction/zero-residual-contraction-spec) (guard 'markov/nnrat-dobrushin-contraction :finite-markov-dobrushin-contraction contraction/contraction-spec) scale/extend-rate-null-prerequisites (guard 'nnrat/zero-of-proper-contraction :nnrat-order-scale scale/zero-of-proper-contraction-spec) (guard 'markov/nnrat-stationary-pointwise-unique-of-proper-contraction :finite-markov-contraction-uniqueness conditional/stationary-unique-of-proper-contraction-spec) (guard 'markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound :finite-markov-ergodic-uniqueness uniqueness/stationary-unique-of-dobrushin-bound-spec) (guard 'markov/nnrat-kernel-iterate :finite-markov-iteration iteration/kernel-iterate-spec) (guard 'markov/nnrat-kernel-iterate-successor :finite-markov-iteration iteration/kernel-iterate-successor-spec) (guard 'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence :finite-markov-iteration iteration/kernel-iterate-preserves-total-mass-spec) (guard-extend 'nnrat/power power/extend-environment) (guard 'nnrat/multiply-associative :nnrat-product-reassociation reassociation/multiply-associative-spec) (guard 'markov/nnrat-stationary-iterate-fixed :finite-markov-stationary-iterate fixed/stationary-iterate-fixed-spec) (guard 'markov/nnrat-kernel-iterate-total-variation-decay :finite-markov-geometric-decay decay/iterate-total-variation-decay-spec) (guard 'markov/nnrat-kernel-iterate-geometric-convergence-to-stationary :finite-markov-geometric-convergence geometric/iterate-converges-to-stationary-spec) (support/extend-with :finite-index-hastings-ergodic theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.index-hastings-ergodic))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
