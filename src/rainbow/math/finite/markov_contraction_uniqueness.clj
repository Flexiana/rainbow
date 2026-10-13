(ns rainbow.math.finite.markov-contraction-uniqueness
  "Stationary-distribution uniqueness, conditional on one named inequality.

  This is the ergodic assembly with the Dobrushin step left ABSTRACT: the
  contraction premise here is exactly the conclusion the in-progress
  Dobrushin module aims at (one kernel application shrinks total variation
  by a proper-fraction factor), taken as a hypothesis at the two stationary
  masses. Nothing about the Dobrushin coefficient is defined or proved
  here; when that inequality lands, instantiating this theorem is one
  application, and uniqueness stops being conditional.

  The proof is the planned composition of the joint lemmas: stationarity
  feeds the total-variation congruence, so the contraction premise rewrites
  to TV <= rho * TV at the same pair; the proper-fraction rate-null law
  forces TV ~ 0; and the separation theorem turns a vanishing total
  variation into pointwise agreement on the carrier. Native and axiom-free
  on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-total-variation :as total-variation]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-equivalence :as order-equivalence]
            [rainbow.math.rational.nnrat.order-scale :as scale]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- mass-type [element] (function/arrow element nnrat))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- rle [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- total-variation [element states left right]
  (app (function/const* 'markov/nnrat-total-variation [U])
       element states left right))
(defn- kernel-step [element states kernel mass]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))

(def stationary-unique-of-proper-contraction-spec
  "The conditional capstone. The contraction premise is demanded only at the
  two stationary masses, the weakest form the assembly needs; a Dobrushin
  theorem quantified over all mass pairs specializes to it directly."
  {:name 'markov/nnrat-stationary-pointwise-unique-of-proper-contraction
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['np nat] ['dp nat]
     ['proper (nat-at-most 'np 'dp)]
     ['left-stationary (stationary 'S 'states 'kernel 'left)]
     ['right-stationary (stationary 'S 'states 'kernel 'right)]
     ['contracts
      (rle (total-variation 'S 'states
                            (kernel-step 'S 'states 'kernel 'left)
                            (kernel-step 'S 'states 'kernel 'right))
           (rmul (make 'np 'dp) (total-variation 'S 'states 'left 'right)))]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (req (app 'left 'state) (app 'right 'state)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['np nat] ['dp nat]
     ['proper (nat-at-most 'np 'dp)]
     ['left-stationary (stationary 'S 'states 'kernel 'left)]
     ['right-stationary (stationary 'S 'states 'kernel 'right)]
     ['contracts
      (rle (total-variation 'S 'states
                            (kernel-step 'S 'states 'kernel 'left)
                            (kernel-step 'S 'states 'kernel 'right))
           (rmul (make 'np 'dp) (total-variation 'S 'states 'left 'right)))]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (let [step-left (kernel-step 'S 'states 'kernel 'left)
          step-right (kernel-step 'S 'states 'kernel 'right)
          tv-pair (total-variation 'S 'states 'left 'right)
          tv-step (total-variation 'S 'states step-left step-right)
          bound (rmul (make 'np 'dp) tv-pair)
          ;; J3 with stationarity as the pointwise agreement:
          ;; TV(step left, step right) ~ TV(left, right).
          step-collapses
          (app (function/const*
                'markov/nnrat-total-variation-respects-pointwise-equivalent
                [U])
               'S 'states
               step-left 'left step-right 'right
               'left-stationary 'right-stationary)
          ;; Transport the contraction premise along the collapse:
          ;; TV(left, right) <= rho * TV(left, right).
          self-bounded
          (app (function/const* 'nnrat/at-most-respects-equivalence [])
               tv-pair tv-step bound bound
               (equivalent-symmetric tv-step tv-pair step-collapses)
               (equivalent-reflexive bound)
               'contracts)
          ;; J2: a value at most a proper multiple of itself is zero.
          vanishes
          (app (function/const* 'nnrat/zero-of-proper-contraction [])
               'np 'dp tv-pair 'proper self-bounded)]
      ;; Separation: vanishing total variation is pointwise agreement.
      (app (function/const*
            'markov/nnrat-total-variation-zero-implies-pointwise-equivalent
            [U])
           'S 'states 'left 'right vanishes 'state 'member)))})

(def definition-specs [])
(def theorem-specs [stationary-unique-of-proper-contraction-spec])

(defn- extend-if-missing [checked-environment marker extend]
  (if (environment/resolve-id checked-environment marker)
    checked-environment
    (extend checked-environment)))

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

;; The rate-null law's own needs, each entered only if absent: the
;; cross-product descent, the strict-below toolkit, and the law itself.
;; The full order-scale extender is deliberately NOT invoked -- its
;; unguarded upstream worlds overlap the total-variation chain.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-total-variation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-if-missing 'nnrat/at-most-to-cross order-equivalence/extend-environment) scale/extend-rate-null-prerequisites (extend-spec-if-missing 'nnrat/zero-of-proper-contraction :nnrat-order-scale scale/zero-of-proper-contraction-spec) (support/extend-with :finite-markov-contraction-uniqueness theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.markov-contraction-uniqueness))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
