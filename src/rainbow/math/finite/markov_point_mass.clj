(ns rainbow.math.finite.markov-point-mass
  "Canonical point masses for finite exact-rational Markov kernels.

  A point mass is the unit diagonal spike induced by a certified Boolean
  equality decision.  On an exhaustive duplicate-free carrier, pushing that
  mass through one kernel step is equivalent to the selected source row.  This
  is the exact bridge from the mass-based iteration API to finite-step
  reachability.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.finite.markov-positive-step :as positive-step]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.diagonal-spike :as spike]
            [rainbow.math.rational.nnrat.map-sum-positive :as positive-sum]
            [rainbow.math.rational.nnrat.map-sum-respects :as map-respects]
            [rainbow.math.rational.nnrat.positive :as positive]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- positive-rational [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- eq-state [element left right]
  (function/equality data-u element left right))
(defn- state-reflexive [element value]
  (app (function/const* 'equality/reflexive [data-u])
       element value))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [U])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- diagonal-spike [element decision mass selected candidate]
  (app (function/const* 'finite/nnrat-diagonal-spike [U])
       element decision mass selected candidate))
(defn- point-mass [element decision selected candidate]
  (app (function/const* 'markov/nnrat-point-mass [U])
       element decision selected candidate))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- left-conjunct [left right both]
  (app (function/const* 'proposition/left []) left right both))

(def point-mass-spec
  {:name 'markov/nnrat-point-mass
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['selected 'S] ['candidate 'S]]
    (diagonal-spike
     'S 'decision
     (function/lam [['ignored 'S]] nnrat-one)
     'selected 'candidate))})

(def point-mass-positive-at-selected-spec
  {:name 'markov/nnrat-point-mass-positive-at-selected
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]]
    (positive-rational
     (point-mass 'S 'decision 'selected 'selected)))
   :value
   (function/lam
    [['S type-u]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]]
    (let [selected-mass
          (point-mass 'S 'decision 'selected 'selected)
          selected-mass-is-one
          (app
           (function/const*
            'finite/nnrat-diagonal-spike-mass-of-equal [U])
           'S 'decision
           (function/lam [['ignored 'S]] nnrat-one)
           'certified 'selected 'selected
           (state-reflexive 'S 'selected))]
      (app
       (function/const* 'nnrat/positive-respects-equivalence [])
       nnrat-one selected-mass
       (equivalent-symmetric
        selected-mass nnrat-one selected-mass-is-one)
       (function/const* 'nnrat/one-positive []))))})

(def kernel-step-point-mass-spec
  {:name 'markov/nnrat-kernel-step-point-mass
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]]
    (req
     (kernel-step
      'S 'states 'kernel
      (function/lam
       [['state 'S]]
       (point-mass 'S 'decision 'selected 'state))
      'target)
     (app 'kernel 'selected 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]]
    (let [items (enumeration 'S 'states)
          row-mass
          (function/lam
           [['source 'S]]
           (app 'kernel 'source 'target))
          product-map
          (function/lam
           [['source 'S]]
           (rmul
            (point-mass 'S 'decision 'selected 'source)
            (app 'kernel 'source 'target)))
          spike-map
          (function/lam
           [['source 'S]]
           (diagonal-spike
            'S 'decision row-mass 'selected 'source))
          certified
          (app
           (function/const*
            'finite/certified-equality-of-exhaustive-carrier [U])
           'S 'states 'decision 'exhaustive)
          pointwise
          (function/lam
           [['source 'S]]
           (app
            (function/const*
             'finite/nnrat-diagonal-unit-spike-multiply [U])
            'S 'decision row-mass certified 'selected 'source))
          products-to-spike
          (app
           (function/const* 'nnrat/map-sum-respects-equivalence [U])
           'S product-map spike-map pointwise items)
          spike-to-row
          (app
           (function/const*
            'finite/nnrat-finset-diagonal-spike-total-of-exhaustive-carrier
            [U])
           'S 'states 'decision row-mass 'exhaustive 'selected)]
      (equivalent-transitive
       (kernel-step
        'S 'states 'kernel
        (function/lam
         [['state 'S]]
         (point-mass 'S 'decision 'selected 'state))
        'target)
       (map-sum 'S spike-map items)
       (app 'kernel 'selected 'target)
       products-to-spike spike-to-row)))})

(def kernel-step-point-mass-positive-spec
  {:name 'markov/nnrat-kernel-step-point-mass-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]
     ['entry-positive
      (positive-rational (app 'kernel 'selected 'target))]]
    (positive-rational
     (kernel-step
      'S 'states 'kernel
      (function/lam
       [['state 'S]]
       (point-mass 'S 'decision 'selected 'state))
      'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]
     ['entry-positive
      (positive-rational (app 'kernel 'selected 'target))]]
    (let [step
          (kernel-step
           'S 'states 'kernel
           (function/lam
            [['state 'S]]
            (point-mass 'S 'decision 'selected 'state))
           'target)
          entry (app 'kernel 'selected 'target)
          step-is-entry
          (app
           (function/const* 'markov/nnrat-kernel-step-point-mass [U])
           'S 'states 'decision 'kernel 'exhaustive 'selected 'target)]
      (app
       (function/const* 'nnrat/positive-respects-equivalence [])
       entry step
       (equivalent-symmetric step entry step-is-entry)
       'entry-positive)))})

(def kernel-iterate-one-point-mass-spec
  {:name 'markov/nnrat-kernel-iterate-one-point-mass
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]]
    (req
     (kernel-iterate
      'S 'states 'kernel (succ zero-nat)
      (function/lam
       [['state 'S]]
       (point-mass 'S 'decision 'selected 'state))
      'target)
     (app 'kernel 'selected 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]]
    (app
     (function/const* 'markov/nnrat-kernel-step-point-mass [U])
     'S 'states 'decision 'kernel 'exhaustive 'selected 'target))})

(def kernel-iterate-one-point-mass-positive-spec
  {:name 'markov/nnrat-kernel-iterate-one-point-mass-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]
     ['entry-positive
      (positive-rational (app 'kernel 'selected 'target))]]
    (positive-rational
     (kernel-iterate
      'S 'states 'kernel (succ zero-nat)
      (function/lam
       [['state 'S]]
       (point-mass 'S 'decision 'selected 'state))
      'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['selected 'S] ['target 'S]
     ['entry-positive
      (positive-rational (app 'kernel 'selected 'target))]]
    (app
     (function/const* 'markov/nnrat-kernel-step-point-mass-positive [U])
     'S 'states 'decision 'kernel 'exhaustive
     'selected 'target 'entry-positive))})

(def kernel-iterate-zero-point-mass-positive-spec
  {:name 'markov/nnrat-kernel-iterate-zero-point-mass-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]]
    (positive-rational
     (kernel-iterate
      'S 'states 'kernel zero-nat
      (function/lam
       [['state 'S]]
       (point-mass 'S 'decision 'selected 'state))
      'selected)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['decision (function/arrow 'S 'S bool)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['certified (certified-equality 'S 'decision)]
     ['selected 'S]]
    (app
     (function/const* 'markov/nnrat-point-mass-positive-at-selected [U])
     'S 'decision 'certified 'selected))})

(def point-mass-iterate-positive-along-trajectory-spec
  (let [trajectory-state
        (fn [step] (app 'trajectory step))]
    {:name 'markov/nnrat-point-mass-iterate-positive-along-trajectory
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['decision (function/arrow 'S 'S bool)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive-rational
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['steps nat]]
      (positive-rational
       (kernel-iterate
        'S 'states 'kernel 'steps
        (function/lam
         [['state 'S]]
         (point-mass
          'S 'decision (trajectory-state zero-nat) 'state))
        (trajectory-state 'steps))))
     :value
     (function/lam
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['decision (function/arrow 'S 'S bool)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['certified (certified-equality 'S 'decision)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive-rational
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['steps nat]]
      (app
       (function/const*
        'markov/nnrat-kernel-iterate-positive-along-trajectory [U])
       'S 'states 'kernel
       (function/lam
        [['state 'S]]
        (point-mass
         'S 'decision (trajectory-state zero-nat) 'state))
       'trajectory 'trajectory-member 'edge-positive
       (app
        (function/const*
         'markov/nnrat-point-mass-positive-at-selected [U])
        'S 'decision 'certified (trajectory-state zero-nat))
       'steps))}))

(def definition-specs [point-mass-spec])
(def theorem-specs
  [point-mass-positive-at-selected-spec
   kernel-step-point-mass-spec
   kernel-step-point-mass-positive-spec
   kernel-iterate-one-point-mass-spec
   kernel-iterate-one-point-mass-positive-spec
   kernel-iterate-zero-point-mass-positive-spec
   point-mass-iterate-positive-along-trajectory-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.diagonal-spike])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/map-sum-respects-equivalence :finite-markov-point-mass-support map-respects/map-sum-respects-spec) (extend-spec-if-missing 'markov/nnrat-kernel-step :finite-markov-point-mass-support stationarity/kernel-step-spec) (extend-spec-if-missing 'markov/nnrat-kernel-iterate :finite-markov-point-mass-support iteration/kernel-iterate-spec) positive/extend-environment (extend-spec-if-missing 'nnrat/map-sum-positive-of-member :finite-markov-point-mass-support positive-sum/map-sum-positive-of-member-spec) (extend-spec-if-missing 'markov/nnrat-kernel-step-positive-of-member :finite-markov-point-mass-support positive-step/kernel-step-positive-of-member-spec) (extend-spec-if-missing 'markov/nnrat-kernel-iterate-positive-successor-of-member :finite-markov-point-mass-support positive-step/kernel-iterate-positive-successor-of-member-spec) (extend-spec-if-missing 'markov/nnrat-kernel-iterate-positive-along-trajectory :finite-markov-point-mass-support positive-step/kernel-iterate-positive-along-trajectory-spec) (support/extend-with :finite-markov-point-mass (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-point-mass))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
