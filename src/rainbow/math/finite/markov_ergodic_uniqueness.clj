(ns rainbow.math.finite.markov-ergodic-uniqueness
  "Uniqueness of stationary distributions under a certified Dobrushin bound.

  The unconditional capstone: for a finite kernel whose Dobrushin
  coefficient is at most a structural proper fraction np/(dp+1), any two
  stationary mass functions of equal total mass agree pointwise on the
  carrier. The proof is one application of the contraction inhabitant to
  discharge the conditional uniqueness theorem's premise at the two
  stationary masses -- the composition specified in
  the design notes, now with no open inequality anywhere
  beneath it. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-contraction-uniqueness :as conditional]
            [rainbow.math.finite.markov-dobrushin-contraction :as contraction]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.order-scale :as scale]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element itemsv value]
  (app (function/const* 'list/membership [U]) element itemsv value))
(defn- mass-type [element] (function/arrow element nnrat))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- make [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make []) numerator denominator-predecessor))
(defn- nat-at-most [left right]
  (app (function/const* 'nat/at-most []) left right))
(defn- total-mass [element states mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element states mass))
(defn- rows-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- coefficient [element states kernel]
  (app (function/const* 'markov/signed-kernel-dobrushin-coefficient [U])
       element states kernel))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- from-nnrat [value]
  (app (function/const* 'signed/from-nnrat []) value))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))

(def stationary-unique-of-dobrushin-bound-spec
  {:name 'markov/nnrat-stationary-pointwise-unique-of-dobrushin-bound
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['np nat] ['dp nat]
     ['proper (nat-at-most 'np 'dp)]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel)
           (from-nnrat (make 'np 'dp)))]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['left-stationary (stationary 'S 'states 'kernel 'left)]
     ['right-stationary (stationary 'S 'states 'kernel 'right)]
     ['equal-total-mass (req (total-mass 'S 'states 'left)
                             (total-mass 'S 'states 'right))]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (req (app 'left 'state) (app 'right 'state)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['np nat] ['dp nat]
     ['proper (nat-at-most 'np 'dp)]
     ['normalized (rows-normalized 'S 'states 'kernel)]
     ['coefficient-bound
      (sle (coefficient 'S 'states 'kernel)
           (from-nnrat (make 'np 'dp)))]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['left-stationary (stationary 'S 'states 'kernel 'left)]
     ['right-stationary (stationary 'S 'states 'kernel 'right)]
     ['equal-total-mass (req (total-mass 'S 'states 'left)
                             (total-mass 'S 'states 'right))]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (let [contracts
          (app (function/const* 'markov/nnrat-dobrushin-contraction [U])
               'S 'states 'kernel (make 'np 'dp)
               'normalized 'coefficient-bound
               'left 'right 'equal-total-mass)]
      (app (function/const*
            'markov/nnrat-stationary-pointwise-unique-of-proper-contraction
            [U])
           'S 'states 'kernel 'left 'right 'np 'dp 'proper
           'left-stationary 'right-stationary contracts
           'state 'member)))})

(def definition-specs [])
(def theorem-specs [stationary-unique-of-dobrushin-bound-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

;; The conditional theorem's own needs, entered per-spec so the
;; contraction chain's worlds are never re-installed wholesale.
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-dobrushin-contraction])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env scale/extend-rate-null-prerequisites (extend-spec-if-missing 'nnrat/zero-of-proper-contraction :nnrat-order-scale scale/zero-of-proper-contraction-spec) (extend-spec-if-missing 'markov/nnrat-stationary-pointwise-unique-of-proper-contraction :finite-markov-contraction-uniqueness conditional/stationary-unique-of-proper-contraction-spec) (support/extend-with :finite-markov-ergodic-uniqueness theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-ergodic-uniqueness))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
