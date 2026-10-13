(ns rainbow.math.finite.markov-iteration
  "Certified finite-horizon iteration of an exact NNRAT Markov kernel.

  `markov/nnrat-kernel-iterate` starts at an arbitrary mass and applies the
  kernel step once per natural-number successor.  Pointwise equivalence is
  preserved through every horizon.  For a normalized kernel, total mass is
  invariant and normalized initial masses remain normalized.  Any stationary
  mass is pointwise invariant under every finite iterate.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-kernel-composition :as composition]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nat (function/const* 'data/Nat []))
(def zero-nat (function/const* 'data/zero []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- kernel-iterate [element states kernel steps mass state]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass state))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- prop-nat-rec [motive base step steps]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step steps))

(def kernel-iterate-spec
  {:name 'markov/nnrat-kernel-iterate
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow nat (function/arrow 'S nnrat)
                    (function/arrow 'S nnrat)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]]
    (app
     (function/const* 'data/Nat.rec [data-u])
     (function/lam [['ignored nat]] (function/arrow 'S nnrat))
     'mass
     (function/lam
      [['ignored-step nat]
       ['previous (function/arrow 'S nnrat)]]
      (function/lam
       [['target 'S]]
       (kernel-step 'S 'states 'kernel 'previous 'target)))
     'steps))})

(def kernel-iterate-zero-spec
  {:name 'markov/nnrat-kernel-iterate-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (req
     (kernel-iterate 'S 'states 'kernel zero-nat 'mass 'state)
     (app 'mass 'state)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (equivalent-reflexive (app 'mass 'state)))})

(def kernel-iterate-successor-spec
  {:name 'markov/nnrat-kernel-iterate-successor
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['target 'S]]
    (req
     (kernel-iterate 'S 'states 'kernel (succ 'steps) 'mass 'target)
     (kernel-step
      'S 'states 'kernel
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state))
      'target)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['target 'S]]
    (equivalent-reflexive
     (kernel-step
      'S 'states 'kernel
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state))
      'target)))})

(def kernel-iterate-respects-mass-spec
  {:name 'markov/nnrat-kernel-iterate-respects-mass-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left-mass (function/arrow 'S nnrat)]
     ['right-mass (function/arrow 'S nnrat)]
     ['same-mass
      (function/forall
       [['state 'S]]
       (req (app 'left-mass 'state)
            (app 'right-mass 'state)))]
     ['steps nat]]
    (function/forall
     [['state 'S]]
     (req
      (kernel-iterate
       'S 'states 'kernel 'steps 'left-mass 'state)
      (kernel-iterate
       'S 'states 'kernel 'steps 'right-mass 'state))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left-mass (function/arrow 'S nnrat)]
     ['right-mass (function/arrow 'S nnrat)]
     ['same-mass
      (function/forall
       [['state 'S]]
       (req (app 'left-mass 'state)
            (app 'right-mass 'state)))]
     ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (function/forall
            [['state 'S]]
            (req
             (kernel-iterate
              'S 'states 'kernel 'n 'left-mass 'state)
             (kernel-iterate
              'S 'states 'kernel 'n 'right-mass 'state))))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (function/lam
            [['target 'S]]
            (app
             (function/const*
              'markov/nnrat-kernel-step-respects-mass-equivalence [U])
             'S 'states 'kernel
             (function/lam
              [['state 'S]]
              (kernel-iterate
               'S 'states 'kernel 'n 'left-mass 'state))
             (function/lam
              [['state 'S]]
              (kernel-iterate
               'S 'states 'kernel 'n 'right-mass 'state))
             'ih 'target)))]
      (prop-nat-rec motive 'same-mass step 'steps)))})

(def kernel-iterate-preserves-total-mass-spec
  {:name 'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]
     ['steps nat]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state)))
     (total-mass 'S 'states 'mass)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]
     ['steps nat]]
    (let [iterate-at
          (fn [n]
            (function/lam
             [['state 'S]]
             (kernel-iterate 'S 'states 'kernel n 'mass 'state)))
          motive
          (function/lam
           [['n nat]]
           (req
            (total-mass 'S 'states (iterate-at 'n))
            (total-mass 'S 'states 'mass)))
          base (equivalent-reflexive (total-mass 'S 'states 'mass))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (let [current (iterate-at 'n)
                 current-total (total-mass 'S 'states current)
                 initial-total (total-mass 'S 'states 'mass)
                 one-step
                 (app
                  (function/const*
                   'markov/nnrat-kernel-step-preserves-total-mass-equivalence
                   [U])
                  'S 'states 'kernel current 'normalized)]
             (equivalent-transitive
              (total-mass 'S 'states (iterate-at (succ 'n)))
              current-total initial-total one-step 'ih)))]
      (prop-nat-rec motive base step 'steps)))})

(def kernel-iterate-preserves-normalization-spec
  {:name 'markov/nnrat-kernel-iterate-preserves-normalization
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['steps nat]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state)))
     nnrat-one))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['steps nat]]
    (equivalent-transitive
     (total-mass
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state)))
     (total-mass 'S 'states 'mass)
     nnrat-one
     (app
      (function/const*
       'markov/nnrat-kernel-iterate-preserves-total-mass-equivalence [U])
      'S 'states 'kernel 'mass 'kernel-normalized 'steps)
     'mass-normalized))})

(def stationary-kernel-iterate-spec
  {:name 'markov/nnrat-stationary-kernel-iterate
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]]
    (function/forall
     [['state 'S]]
     (req
      (kernel-iterate 'S 'states 'kernel 'steps 'mass 'state)
      (app 'mass 'state))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]]
    (let [iterate-at
          (fn [n]
            (function/lam
             [['state 'S]]
             (kernel-iterate 'S 'states 'kernel n 'mass 'state)))
          motive
          (function/lam
           [['n nat]]
           (function/forall
            [['state 'S]]
            (req (app (iterate-at 'n) 'state)
                 (app 'mass 'state))))
          base
          (function/lam
           [['state 'S]]
           (equivalent-reflexive (app 'mass 'state)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (function/lam
            [['target 'S]]
            (let [current (iterate-at 'n)
                  next (kernel-step 'S 'states 'kernel current 'target)
                  mass-step (kernel-step 'S 'states 'kernel 'mass 'target)
                  transport
                  (app
                   (function/const*
                    'markov/nnrat-kernel-step-respects-mass-equivalence [U])
                   'S 'states 'kernel current 'mass 'ih 'target)]
              (equivalent-transitive
               next mass-step (app 'mass 'target)
               transport (app 'fixed 'target)))))]
      (prop-nat-rec motive base step 'steps)))})

(def definition-specs [kernel-iterate-spec])

(def theorem-specs
  [kernel-iterate-zero-spec
   kernel-iterate-successor-spec
   kernel-iterate-respects-mass-spec
   kernel-iterate-preserves-total-mass-spec
   kernel-iterate-preserves-normalization-spec
   stationary-kernel-iterate-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-kernel-composition])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-iteration (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-iteration))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
