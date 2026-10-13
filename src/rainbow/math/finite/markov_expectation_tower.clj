(ns rainbow.math.finite.markov-expectation-tower
  "The exact finite Markov expectation tower law over NNRAT.

  A kernel averages an observable backward while it pushes a mass forward.
  Finite Fubini proves these are adjoint operations:

    E_(mu K)[f] ~ E_mu[K f].

  Combining this with stationarity proves E_mu[K f] ~ E_mu[f] for every
  observable.  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.markov-expectation-invariance :as invariance]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))

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
(defn- expectation [element states mass observable]
  (app (function/const* 'probability/nnrat-expectation [U])
       element states mass observable))
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-observable [element states kernel observable source]
  (app (function/const* 'markov/nnrat-kernel-observable [U])
       element states kernel observable source))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
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
(defn- map-sum-respects [element left right pointwise items]
  (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
       element left right pointwise items))
(defn- scale-right [element mapping scalar items]
  (app (function/const* 'nnrat/map-sum-scale-right [U])
       element mapping scalar items))
(defn- sum-swap [left-element right-element mapping left-items right-items]
  (app (function/const* 'nnrat/map-sum-swap [U])
       left-element right-element mapping left-items right-items))

;; ((mass * kernel) * value) ~ ((value * kernel) * mass).
(defn- reorder-flow [mass kernel value]
  (let [start (rmul (rmul mass kernel) value)
        mass-value (rmul (rmul mass value) kernel)
        value-mass (rmul (rmul value mass) kernel)
        finish (rmul (rmul value kernel) mass)]
    (equivalent-transitive
     start mass-value finish
     (app (function/const* 'nnrat/multiply-swap-right [])
          mass kernel value)
     (equivalent-transitive
      mass-value value-mass finish
      (multiply-respects
       (rmul mass value) (rmul value mass)
       kernel kernel
       (app (function/const* 'nnrat/multiply-commutative []) mass value)
       (equivalent-reflexive kernel))
      (app (function/const* 'nnrat/multiply-swap-right [])
           value mass kernel)))))

(def kernel-observable-spec
  {:name 'markov/nnrat-kernel-observable
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]]
    (function/arrow 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]
     ['source 'S]]
    (expectation 'S 'states (app 'kernel 'source) 'observable))})

(def expectation-after-kernel-step-spec
  {:name 'markov/nnrat-expectation-after-kernel-step
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]]
    (req
     (expectation
      'S 'states
      (function/lam
       [['target 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'target))
      'observable)
     (expectation
      'S 'states 'mass
      (function/lam
       [['source 'S]]
       (kernel-observable 'S 'states 'kernel 'observable 'source)))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['observable (function/arrow 'S nnrat)]]
    (let [items (enumeration 'S 'states)
          left-map
          (function/lam
           [['target 'S]]
           (rmul
            (app 'observable 'target)
            (kernel-step 'S 'states 'kernel 'mass 'target)))
          ordered-inner
          (fn [target]
            (function/lam
             [['source 'S]]
             (rmul
              (rmul (app 'observable target)
                    (app 'kernel 'source target))
              (app 'mass 'source))))
          ordered-map
          (function/lam
           [['target 'S]]
           (map-sum 'S (ordered-inner 'target) items))
          ordered-double (map-sum 'S ordered-map items)
          expand-target
          (function/lam
           [['target 'S]]
           (let [observable-at-target (app 'observable 'target)
                 incoming
                 (function/lam
                  [['source 'S]]
                  (rmul (app 'mass 'source)
                        (app 'kernel 'source 'target)))
                 incoming-total (map-sum 'S incoming items)
                 scaled-total (rmul incoming-total observable-at-target)
                 scaled-inner
                 (function/lam
                  [['source 'S]]
                  (rmul (app incoming 'source) observable-at-target))
                 scaled-sum (map-sum 'S scaled-inner items)
                 ordered-sum (map-sum 'S (ordered-inner 'target) items)
                 commute
                 (app (function/const* 'nnrat/multiply-commutative [])
                      observable-at-target incoming-total)
                 distribute
                 (scale-right 'S incoming observable-at-target items)
                 reorder
                 (map-sum-respects
                  'S scaled-inner (ordered-inner 'target)
                  (function/lam
                   [['source 'S]]
                   (reorder-flow
                    (app 'mass 'source)
                    (app 'kernel 'source 'target)
                    observable-at-target))
                  items)]
             (equivalent-transitive
              (rmul observable-at-target incoming-total)
              scaled-total ordered-sum commute
              (equivalent-transitive
               scaled-total scaled-sum ordered-sum
               distribute reorder))))
          expand-all
          (map-sum-respects 'S left-map ordered-map expand-target items)
          flow
          (function/lam
           [['target 'S]]
           (ordered-inner 'target))
          swapped-inner
          (fn [source]
            (function/lam
             [['target 'S]]
             (rmul
              (rmul (app 'observable 'target)
                    (app 'kernel source 'target))
              (app 'mass source))))
          swapped-map
          (function/lam
           [['source 'S]]
           (map-sum 'S (swapped-inner 'source) items))
          swapped-double (map-sum 'S swapped-map items)
          swap-proof (sum-swap 'S 'S flow items items)
          right-map
          (function/lam
           [['source 'S]]
           (rmul
            (kernel-observable 'S 'states 'kernel 'observable 'source)
            (app 'mass 'source)))
          factor-source
          (function/lam
           [['source 'S]]
           (equivalent-symmetric
            (app right-map 'source)
            (app swapped-map 'source)
            (scale-right
             'S
             (function/lam
              [['target 'S]]
              (rmul (app 'observable 'target)
                    (app 'kernel 'source 'target)))
             (app 'mass 'source) items)))
          factor-all
          (map-sum-respects 'S swapped-map right-map factor-source items)]
      (equivalent-transitive
       (expectation
        'S 'states
        (function/lam
         [['target 'S]]
         (kernel-step 'S 'states 'kernel 'mass 'target))
        'observable)
       ordered-double
       (expectation
        'S 'states 'mass
        (function/lam
         [['source 'S]]
         (kernel-observable 'S 'states 'kernel 'observable 'source)))
       expand-all
       (equivalent-transitive
        ordered-double swapped-double
        (expectation
         'S 'states 'mass
         (function/lam
          [['source 'S]]
          (kernel-observable 'S 'states 'kernel 'observable 'source)))
        swap-proof factor-all))))})

(def stationary-kernel-observable-expectation-spec
  {:name 'markov/nnrat-stationary-kernel-observable-expectation
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['observable (function/arrow 'S nnrat)]]
    (req
     (expectation
      'S 'states 'mass
      (function/lam
       [['source 'S]]
       (kernel-observable 'S 'states 'kernel 'observable 'source)))
     (expectation 'S 'states 'mass 'observable)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['observable (function/arrow 'S nnrat)]]
    (let [stepped
          (function/lam
           [['target 'S]]
           (kernel-step 'S 'states 'kernel 'mass 'target))
          stepped-expectation
          (expectation 'S 'states stepped 'observable)
          averaged-expectation
          (expectation
           'S 'states 'mass
           (function/lam
            [['source 'S]]
            (kernel-observable
             'S 'states 'kernel 'observable 'source)))
          original-expectation
          (expectation 'S 'states 'mass 'observable)
          tower
          (app
           (function/const* 'markov/nnrat-expectation-after-kernel-step [U])
           'S 'states 'kernel 'mass 'observable)
          invariant
          (app
           (function/const*
            'markov/nnrat-stationary-step-expectation-invariant [U])
           'S 'states 'kernel 'mass 'fixed 'observable)]
      (equivalent-transitive
       averaged-expectation stepped-expectation original-expectation
       (equivalent-symmetric
        stepped-expectation averaged-expectation tower)
       invariant)))})

(def definition-specs [kernel-observable-spec])

(def theorem-specs
  [expectation-after-kernel-step-spec
   stationary-kernel-observable-expectation-spec])

(defn extend-environment [env]
  (-> env
      invariance/extend-environment
      (support/extend-with
       :finite-markov-expectation-tower
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
