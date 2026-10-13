(ns rainbow.math.finite.markov-stationarity
  "Exact finite NNRAT Markov kernels, detailed balance, and stationarity.

  `markov/nnrat-kernel-step` pushes a mass function through a finite kernel.
  Kernel normalization is rowwise total mass one.  Detailed balance equates
  every directed probability flow with its reverse.  Summing those checked
  pairwise equivalences and factoring the target mass proves stationarity.

  The module also gives pointwise congruence of the step in both its mass and
  kernel arguments, and proves that a stationary normalized mass remains
  normalized after a step.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.environment :as environment]
            [rainbow.math.finite.bellman-value-optimality
             :as finite-probability]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- total-mass [element source mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element source mass))
(defn- kernel-step [element source kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element source kernel mass target))
(defn- kernel-normalized [element source kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element source kernel))
(defn- detailed-balance [element mass kernel]
  (app (function/const* 'markov/nnrat-detailed-balance [U])
       element mass kernel))
(defn- stationary [element source kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element source kernel mass))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- multiply-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       left equivalent-left right equivalent-right same-left same-right))
(defn- map-sum-respects [element left right pointwise items]
  (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
       element left right pointwise items))

(def kernel-step-spec
  {:name 'markov/nnrat-kernel-step
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]]
    (function/arrow 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['target 'S]]
    (map-sum
     'S
     (function/lam
      [['source 'S]]
      (rmul (app 'mass 'source)
            (app 'kernel 'source 'target)))
     (enumeration 'S 'states)))})

(def kernel-rows-normalized-spec
  {:name 'markov/nnrat-kernel-rows-normalized
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['state 'S]]
     (req (total-mass 'S 'states (app 'kernel 'state))
          nnrat-one)))})

(def detailed-balance-spec
  {:name 'markov/nnrat-detailed-balance
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['mass (function/arrow 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['mass (function/arrow 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['left 'S] ['right 'S]]
     (req
      (rmul (app 'mass 'left) (app 'kernel 'left 'right))
      (rmul (app 'mass 'right) (app 'kernel 'right 'left)))))})

(def stationary-spec
  {:name 'markov/nnrat-stationary
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]]
    (function/forall
     [['state 'S]]
     (req (kernel-step 'S 'states 'kernel 'mass 'state)
          (app 'mass 'state))))})

(def kernel-step-respects-mass-spec
  {:name 'markov/nnrat-kernel-step-respects-mass-equivalence
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
            (app 'right-mass 'state)))]]
    (function/forall
     [['target 'S]]
     (req
      (kernel-step 'S 'states 'kernel 'left-mass 'target)
      (kernel-step 'S 'states 'kernel 'right-mass 'target))))
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
            (app 'right-mass 'state)))]]
    (function/lam
     [['target 'S]]
     (map-sum-respects
      'S
      (function/lam
       [['source 'S]]
       (rmul (app 'left-mass 'source)
             (app 'kernel 'source 'target)))
      (function/lam
       [['source 'S]]
       (rmul (app 'right-mass 'source)
             (app 'kernel 'source 'target)))
      (function/lam
       [['source 'S]]
       (multiply-respects
        (app 'left-mass 'source) (app 'right-mass 'source)
        (app 'kernel 'source 'target) (app 'kernel 'source 'target)
        (app 'same-mass 'source)
        (equivalent-reflexive (app 'kernel 'source 'target))))
      (enumeration 'S 'states))))})

(def kernel-step-respects-kernel-spec
  {:name 'markov/nnrat-kernel-step-respects-kernel-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-kernel (function/arrow 'S 'S nnrat)]
     ['right-kernel (function/arrow 'S 'S nnrat)]
     ['same-kernel
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-kernel 'source 'target)
            (app 'right-kernel 'source 'target)))]
     ['mass (function/arrow 'S nnrat)]]
    (function/forall
     [['target 'S]]
     (req
      (kernel-step 'S 'states 'left-kernel 'mass 'target)
      (kernel-step 'S 'states 'right-kernel 'mass 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-kernel (function/arrow 'S 'S nnrat)]
     ['right-kernel (function/arrow 'S 'S nnrat)]
     ['same-kernel
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-kernel 'source 'target)
            (app 'right-kernel 'source 'target)))]
     ['mass (function/arrow 'S nnrat)]]
    (function/lam
     [['target 'S]]
     (map-sum-respects
      'S
      (function/lam
       [['source 'S]]
       (rmul (app 'mass 'source)
             (app 'left-kernel 'source 'target)))
      (function/lam
       [['source 'S]]
       (rmul (app 'mass 'source)
             (app 'right-kernel 'source 'target)))
      (function/lam
       [['source 'S]]
       (multiply-respects
        (app 'mass 'source) (app 'mass 'source)
        (app 'left-kernel 'source 'target)
        (app 'right-kernel 'source 'target)
        (equivalent-reflexive (app 'mass 'source))
        (app 'same-kernel 'source 'target)))
      (enumeration 'S 'states))))})

(def kernel-step-respects-spec
  {:name 'markov/nnrat-kernel-step-respects-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-kernel (function/arrow 'S 'S nnrat)]
     ['right-kernel (function/arrow 'S 'S nnrat)]
     ['same-kernel
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-kernel 'source 'target)
            (app 'right-kernel 'source 'target)))]
     ['left-mass (function/arrow 'S nnrat)]
     ['right-mass (function/arrow 'S nnrat)]
     ['same-mass
      (function/forall
       [['state 'S]]
       (req (app 'left-mass 'state)
            (app 'right-mass 'state)))]]
    (function/forall
     [['target 'S]]
     (req
      (kernel-step 'S 'states 'left-kernel 'left-mass 'target)
      (kernel-step 'S 'states 'right-kernel 'right-mass 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['left-kernel (function/arrow 'S 'S nnrat)]
     ['right-kernel (function/arrow 'S 'S nnrat)]
     ['same-kernel
      (function/forall
       [['source 'S] ['target 'S]]
       (req (app 'left-kernel 'source 'target)
            (app 'right-kernel 'source 'target)))]
     ['left-mass (function/arrow 'S nnrat)]
     ['right-mass (function/arrow 'S nnrat)]
     ['same-mass
      (function/forall
       [['state 'S]]
       (req (app 'left-mass 'state)
            (app 'right-mass 'state)))]]
    (function/lam
     [['target 'S]]
     (let [middle
           (kernel-step 'S 'states 'left-kernel 'right-mass 'target)
           mass-step
           (app
            (function/const*
             'markov/nnrat-kernel-step-respects-mass-equivalence [U])
            'S 'states 'left-kernel
            'left-mass 'right-mass 'same-mass 'target)
           kernel-step-proof
           (app
            (function/const*
             'markov/nnrat-kernel-step-respects-kernel-equivalence [U])
            'S 'states 'left-kernel 'right-kernel 'same-kernel
            'right-mass 'target)]
       (equivalent-transitive
        (kernel-step 'S 'states 'left-kernel 'left-mass 'target)
        middle
        (kernel-step 'S 'states 'right-kernel 'right-mass 'target)
        mass-step kernel-step-proof))))})

(def detailed-balance-implies-stationary-spec
  {:name 'markov/nnrat-detailed-balance-implies-stationary
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]
     ['balanced (detailed-balance 'S 'mass 'kernel)]]
    (stationary 'S 'states 'kernel 'mass))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]
     ['balanced (detailed-balance 'S 'mass 'kernel)]]
    (function/lam
     [['target 'S]]
     (let [items (enumeration 'S 'states)
           forward
           (function/lam
            [['source 'S]]
            (rmul (app 'mass 'source)
                  (app 'kernel 'source 'target)))
           reverse
           (function/lam
            [['source 'S]]
            (rmul (app 'mass 'target)
                  (app 'kernel 'target 'source)))
           commuted
           (function/lam
            [['source 'S]]
            (rmul (app 'kernel 'target 'source)
                  (app 'mass 'target)))
           reverse-sum (map-sum 'S reverse items)
           commuted-sum (map-sum 'S commuted items)
           row-total
           (total-mass 'S 'states (app 'kernel 'target))
           scaled-total (rmul row-total (app 'mass 'target))
           one-scaled (rmul nnrat-one (app 'mass 'target))
           balance-sum
           (map-sum-respects
            'S forward reverse
            (function/lam
             [['source 'S]]
             (app 'balanced 'source 'target))
            items)
           commute-sum
           (map-sum-respects
            'S reverse commuted
            (function/lam
             [['source 'S]]
             (app (function/const* 'nnrat/multiply-commutative [])
                  (app 'mass 'target)
                  (app 'kernel 'target 'source)))
            items)
           factor
           (equivalent-symmetric
            scaled-total commuted-sum
            (app (function/const* 'nnrat/map-sum-scale-right [U])
                 'S (app 'kernel 'target) (app 'mass 'target) items))
           normalize-product
           (multiply-respects
            row-total nnrat-one
            (app 'mass 'target) (app 'mass 'target)
            (app 'normalized 'target)
            (equivalent-reflexive (app 'mass 'target)))
           remove-one
           (app (function/const* 'nnrat/multiply-one-left [])
                (app 'mass 'target))]
       (equivalent-transitive
        (kernel-step 'S 'states 'kernel 'mass 'target)
        reverse-sum (app 'mass 'target)
        balance-sum
        (equivalent-transitive
         reverse-sum commuted-sum (app 'mass 'target)
         commute-sum
         (equivalent-transitive
          commuted-sum scaled-total (app 'mass 'target)
          factor
          (equivalent-transitive
           scaled-total one-scaled (app 'mass 'target)
           normalize-product remove-one)))))))})

(def stationary-step-normalized-spec
  {:name 'markov/nnrat-stationary-step-normalized
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['mass-normalized
      (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['state 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'state)))
     nnrat-one))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['mass-normalized
      (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]]
    (let [step-mass
          (function/lam
           [['state 'S]]
           (kernel-step 'S 'states 'kernel 'mass 'state))
          same-total
          (map-sum-respects
           'S step-mass 'mass
           (function/lam
            [['state 'S]]
            (app 'fixed 'state))
           (enumeration 'S 'states))]
      (equivalent-transitive
       (total-mass 'S 'states step-mass)
       (total-mass 'S 'states 'mass)
       nnrat-one same-total 'mass-normalized)))})

(def definition-specs
  [kernel-step-spec
   kernel-rows-normalized-spec
   detailed-balance-spec
   stationary-spec])

(def theorem-specs
  [kernel-step-respects-mass-spec
   kernel-step-respects-kernel-spec
   kernel-step-respects-spec
   detailed-balance-implies-stationary-spec
   stationary-step-normalized-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(defn extend-environment [env]
  (-> env
      finite-probability/extend-environment
      (extend-spec-if-missing
       'nnrat/multiply-one-left :nnrat-identities
       identities/multiply-one-left-spec)
      (support/extend-with
       :finite-markov-stationarity
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
