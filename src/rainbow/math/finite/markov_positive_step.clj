(ns rainbow.math.finite.markov-positive-step
  "Positive support propagation through a finite exact-rational kernel.

  If a listed source has positive current mass and a positive transition to a
  target, then one kernel step has positive mass at that target.  Other source
  contributions are merely nonnegative and cannot destroy the witness.  This
  is the reusable induction step for finite positive paths and reachability.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-iteration :as iteration]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.map-sum-positive :as positive-sum]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-iterate [element states kernel steps mass target]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass target))

(def kernel-step-positive-of-member-spec
  {:name 'markov/nnrat-kernel-step-positive-of-member
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['source 'S] ['target 'S]
     ['source-member
      (membership 'S (enumeration 'S 'states) 'source)]
     ['source-positive (positive (app 'mass 'source))]
     ['edge-positive (positive (app 'kernel 'source 'target))]]
    (positive (kernel-step 'S 'states 'kernel 'mass 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['source 'S] ['target 'S]
     ['source-member
      (membership 'S (enumeration 'S 'states) 'source)]
     ['source-positive (positive (app 'mass 'source))]
     ['edge-positive (positive (app 'kernel 'source 'target))]]
    (let [transition-products
          (function/lam
           [['candidate 'S]]
           (rmul
            (app 'mass 'candidate)
            (app 'kernel 'candidate 'target)))
          source-product-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'mass 'source)
           (app 'kernel 'source 'target)
           'source-positive 'edge-positive)]
      (app
       (function/const* 'nnrat/map-sum-positive-of-member [U])
       'S transition-products (enumeration 'S 'states)
       'source 'source-member source-product-positive)))})

(def kernel-iterate-positive-successor-of-member-spec
  {:name 'markov/nnrat-kernel-iterate-positive-successor-of-member
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['steps nat]
     ['middle 'S] ['target 'S]
     ['middle-member
      (membership 'S (enumeration 'S 'states) 'middle)]
     ['middle-positive
      (positive
       (kernel-iterate
        'S 'states 'kernel 'steps 'mass 'middle))]
     ['edge-positive (positive (app 'kernel 'middle 'target))]]
    (positive
     (kernel-iterate
      'S 'states 'kernel (succ 'steps) 'mass 'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['steps nat]
     ['middle 'S] ['target 'S]
     ['middle-member
      (membership 'S (enumeration 'S 'states) 'middle)]
     ['middle-positive
      (positive
       (kernel-iterate
        'S 'states 'kernel 'steps 'mass 'middle))]
     ['edge-positive (positive (app 'kernel 'middle 'target))]]
    (app
     (function/const* 'markov/nnrat-kernel-step-positive-of-member [U])
     'S 'states 'kernel
     (function/lam
      [['state 'S]]
      (kernel-iterate
       'S 'states 'kernel 'steps 'mass 'state))
     'middle 'target 'middle-member
     'middle-positive 'edge-positive))})

(def kernel-iterate-positive-along-trajectory-spec
  (let [trajectory-state
        (fn [step] (app 'trajectory step))
        motive
        (function/lam
         [['steps nat]]
         (positive
          (kernel-iterate
           'S 'states 'kernel 'steps 'mass
           (trajectory-state 'steps))))]
    {:name 'markov/nnrat-kernel-iterate-positive-along-trajectory
     :universes ['u]
     :type
     (function/forall
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['mass (function/arrow 'S nnrat)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['initial-positive
        (positive (app 'mass (trajectory-state zero-nat)))]
       ['steps nat]]
      (positive
       (kernel-iterate
        'S 'states 'kernel 'steps 'mass
        (trajectory-state 'steps))))
     :value
     (function/lam
      [['S type-u]
       ['states (exact-finset-of 'S)]
       ['kernel (function/arrow 'S 'S nnrat)]
       ['mass (function/arrow 'S nnrat)]
       ['trajectory (function/arrow nat 'S)]
       ['trajectory-member
        (function/forall
         [['step nat]]
         (membership
          'S (enumeration 'S 'states) (trajectory-state 'step)))]
       ['edge-positive
        (function/forall
         [['step nat]]
         (positive
          (app 'kernel
               (trajectory-state 'step)
               (trajectory-state (succ 'step)))))]
       ['initial-positive
        (positive (app 'mass (trajectory-state zero-nat)))]
       ['steps nat]]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       'initial-positive
       (function/lam
        [['step nat]
         ['induction-hypothesis (app motive 'step)]]
        (app
         (function/const*
          'markov/nnrat-kernel-iterate-positive-successor-of-member [U])
         'S 'states 'kernel 'mass 'step
         (trajectory-state 'step)
         (trajectory-state (succ 'step))
         (app 'trajectory-member 'step)
         'induction-hypothesis
         (app 'edge-positive 'step)))
       'steps))}))

(def definition-specs [])
(def theorem-specs
  [kernel-step-positive-of-member-spec
   kernel-iterate-positive-successor-of-member-spec
   kernel-iterate-positive-along-trajectory-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.map-sum-positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'markov/nnrat-kernel-step :finite-markov-positive-step-support stationarity/kernel-step-spec) (extend-spec-if-missing 'markov/nnrat-kernel-iterate :finite-markov-positive-step-support iteration/kernel-iterate-spec) (support/extend-with :finite-markov-positive-step theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-positive-step))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
