(ns rainbow.math.finite.markov-dobrushin
  "Maximum of a supplied NNRAT distance list, for a finite Dobrushin coefficient.

  The list fold and its conditional bounds are checked here. Complete row
  coefficients and contraction are proved in finite-markov-dobrushin-kernel
  and finite-markov-dobrushin-contraction; metadata below points to them."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.rational :as signed-rational]
            [rainbow.math.rational.signed.order :as signed-order]
            [rainbow.math.rational.signed.unit-laws :as signed-units]
            [rainbow.math.rational.signed.vector-sup-distance :as signed-max]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element] (app (function/const* 'data/List [type-level]) element))
(defn- nil-list [element]
  (app (function/const* 'data/nil [type-level]) element))
(defn- signed-map-max [element mapping items]
  (app (function/const* 'list/signed-map-max [zero-level]) element mapping items))
(defn- from-nnrat [value] (app (function/const* 'signed/from-nnrat []) value))
(defn- sle [left right]
  (app (function/const* 'signed/at-most []) left right))
(defn- membership [source value]
  (app (function/const* 'list/membership [zero-level]) nnrat source value))
(defn- coefficient [carrier distances]
  (app (function/const* 'markov/signed-dobrushin-coefficient [U])
       carrier distances))

(defn- pointwise-bound [distances upper]
  (function/forall
   [['distance nnrat] ['member (membership distances 'distance)]]
   (sle (from-nnrat 'distance) upper)))

(def dobrushin-coefficient-spec
  {:name 'markov/signed-dobrushin-coefficient :kind :definition
   :universes ['u] :transparency :reducible
   ;; The carrier is polymorphic, but the folded values are NNRATs at the
   ;; fixed zero universe.  Consequently this list/fold must remain at
   ;; `type-level`/`zero-level`; passing the carrier universe is rejected by
   ;; the kernel (the element sort is not the carrier sort).
   :type (function/forall [['S type-u] ['distances (list-of nnrat)]] signed)
   :value (function/lam [['S type-u] ['distances (list-of nnrat)]]
            (signed-map-max nnrat
              (function/lam [['distance nnrat]] (from-nnrat 'distance))
              'distances))})

(def dobrushin-coefficient-nonnegative-spec
  {:name 'markov/signed-dobrushin-coefficient-nonnegative :kind :theorem
   :universes ['u]
   :type (function/forall [['S type-u] ['distances (list-of nnrat)]]
           (app (function/const* 'signed/at-most [])
                (function/const* 'signed/zero [])
                (app (function/const* 'markov/signed-dobrushin-coefficient [U])
                     'S 'distances)))
   :value (function/lam [['S type-u] ['distances (list-of nnrat)]]
            (app (function/const* 'list/signed-map-max-nonnegative [zero-level])
                 nnrat (function/lam [['distance nnrat]] (from-nnrat 'distance))
            'distances))})

(def dobrushin-coefficient-empty-spec
  {:name 'markov/signed-dobrushin-coefficient-empty
   :kind :theorem :universes ['u]
   :type
   (function/forall
    [['S type-u]]
    (app (function/const* 'signed/equivalent [])
         (app (function/const* 'markov/signed-dobrushin-coefficient [U])
              'S (nil-list nnrat))
         (function/const* 'signed/zero [])))
   :value
   (function/lam
    [['S type-u]]
    (app (function/const* 'list/signed-map-max-empty [zero-level])
         nnrat
         (function/lam [['distance nnrat]] (from-nnrat 'distance))))})

(def dobrushin-coefficient-bounded-spec
  (let [bindings [['S type-u] ['distances (list-of nnrat)]
                  ['upper signed]
                  ['zero-upper (sle (function/const* 'signed/zero []) 'upper)]
                  ['pointwise (pointwise-bound 'distances 'upper)]]]
    {:name 'markov/signed-dobrushin-coefficient-bounded
     :kind :theorem :universes ['u]
     :type (function/forall bindings
             (sle (coefficient 'S 'distances) 'upper))
     :value
     (function/lam bindings
       (app (function/const* 'list/signed-map-max-bounded [zero-level])
            nnrat (function/lam [['distance nnrat]] (from-nnrat 'distance))
            'upper 'zero-upper 'distances 'pointwise))}))

(def dobrushin-coefficient-at-most-one-of-pointwise-spec
  (let [one (function/const* 'signed/one [])
        bindings [['S type-u] ['distances (list-of nnrat)]
                  ['pointwise (pointwise-bound 'distances one)]]]
    {:name 'markov/signed-dobrushin-coefficient-at-most-one-of-pointwise
     :kind :theorem :universes ['u]
     :type (function/forall bindings
             (sle (coefficient 'S 'distances) one))
     :value
     (function/lam bindings
       (app (function/const* 'markov/signed-dobrushin-coefficient-bounded [U])
            'S 'distances one
            (function/const* 'signed/zero-at-most-one []) 'pointwise))}))

;; Evidence metadata, not a proof term. The named producer must be loaded
;; and its theorem kernel-checked before any consumer counts this result.
(def markov-contraction-statement
  {:id :markov/finite-dobrushin-contraction
   :kind :theorem-evidence
   :hypotheses [:finite-carrier
                :stochastic-kernel
                :nonnegative-rational-mass-functions
                :equal-total-mass
                :dobrushin-coefficient-at-most-rho]
   :strict-contraction-condition :rho-strictly-less-than-one
   :conclusion :total-variation-contraction
   :formula "TV(mu K, nu K) <= rho * TV(mu, nu)"
   :distance-convention :half-l1
   :kernel-distance-convention :l1
   :coefficient-bounds ["0 <= delta(K)" "delta(K) <= 1"]
   :proved-coefficient-bounds ["0 <= delta(K)" "delta(K) <= 1"]
   :formal-predicate 'markov/nnrat-dobrushin-contraction-estimate
   :proof-theorem 'markov/nnrat-dobrushin-contraction
   :producer 'rainbow.math.finite.markov-dobrushin-contraction
   :conditional-bound-theorems
   ['markov/signed-dobrushin-coefficient-bounded
    'markov/signed-dobrushin-coefficient-at-most-one-of-pointwise]
   :status :proved})

;; Both coefficient obligations are now proved for the constructed row maximum.
(def dobrushin-coefficient-bound-obligations
  [{:id :markov/dobrushin-nonnegative
    :statement "0 <= delta(K)"
    :status :proved
    :required-lemma 'list/signed-map-max-nonnegative
    :elaboration-gap nil}
   {:id :markov/dobrushin-at-most-one
    :statement "delta(K) <= 1"
    :status :proved
    :theorem 'markov/signed-kernel-dobrushin-coefficient-at-most-one
    :producer 'rainbow.math.finite.markov-dobrushin-kernel
    :required-lemma 'list/signed-map-max-bounded
    :required-provider 'rainbow.math.rational.signed.geometric-bridge
    :sub-obligations [:nnrat-row-distance-at-most-one
                      'signed/from-nnrat-at-most
                      :pointwise-bound-on-enumerated-rows]
    :elaboration-gap nil}])

;; The fixed NNRAT fold instantiates the generic bounded lemma at zero.
;; There is no missing universe foundation; the constructive proof is landed.
(def dobrushin-coefficient-proof-plan
  {:carrier-specialization :successor-universe-list
   :fold-bridge 'list/signed-map-max
   :nonnegative-step 'list/signed-map-max-nonnegative
   :upper-bound-step 'markov/row-total-variation-at-most-one
   :contraction-step :finite-total-variation-map-sum
   ;; Once residual masses are enumerated, this generic axiom-free bridge
   ;; supplies the scalar mixture inequality used by the contraction step.
   :weighted-mixture-bound 'nnrat/weighted-sum-scaled-at-most
   :residual-expansion-obligation
   {:status :proved
    :hypotheses [:equal-total-mass :stochastic-kernel
                 :dobrushin-coefficient-at-most-rho]
    :conclusion
    "L1(step left, step right) <= rho * L1(left,right)"
    :required-bridge
    "rewrite kernel-step TV through common mass, then apply finite residual mixture"
    :proved-components
    ['markov/nnrat-kernel-step-left-residual-decomposition
     'markov/nnrat-kernel-step-right-residual-decomposition
     'markov/nnrat-kernel-step-total-variation-residual
     'markov/nnrat-kernel-step-residual-expansion-bound
     'markov/nnrat-kernel-step-residual-weighted-expansion-bound
     'markov/nnrat-kernel-step-coupling-distance-bound
     'markov/nnrat-kernel-step-positive-residual-contraction
     'markov/nnrat-kernel-step-zero-residual-contraction
     'markov/nnrat-dobrushin-contraction]
    :remaining-step nil
    :remaining-formula nil
    :producer 'rainbow.math.finite.markov-dobrushin-contraction}
   :status :proved
   :current-gap nil})

(def dobrushin-list-universe-bridge
  {:coefficient-element :nnrat
   :coefficient-element-universe :zero
   :coefficient-list-type :data-list
   :coefficient-list-level :succ-zero
   :bounded-lemma-specialization :zero
   :bounded-lemma-carrier-universe :polymorphic
   :status :proved
   :theorem 'markov/signed-dobrushin-coefficient-bounded
   :required-adaptation nil})

(def definition-specs [dobrushin-coefficient-spec])
;; Every registered theorem has a proof term checked by support/extend-with.
(def theorem-specs [dobrushin-coefficient-nonnegative-spec
                    dobrushin-coefficient-empty-spec
                    dobrushin-coefficient-bounded-spec
                    dobrushin-coefficient-at-most-one-of-pointwise-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.signed.rational rainbow.math.rational.signed.order rainbow.math.rational.signed.vector-sup-distance rainbow.math.rational.signed.unit-laws])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-dobrushin (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-dobrushin))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
