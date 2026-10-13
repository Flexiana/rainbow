(ns rainbow.math.finite.markov-kernel-composition
  "Composition laws for exact finite NNRAT Markov kernels.

  The first kernel is applied before the second:

    (K ; L)(source,target) = sum_middle K(source,middle) * L(middle,target).

  Finite Fubini and distributivity prove both Chapman--Kolmogorov and exact
  preservation of total mass.  Consequently normalized kernels are closed
  under composition, normalized masses remain normalized after every step,
  and a mass stationary for each factor is stationary for their composition.
  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.fubini :as fubini]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]))

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
(defn- kernel-step [element states kernel mass target]
  (app (function/const* 'markov/nnrat-kernel-step [U])
       element states kernel mass target))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- kernel-compose [element states first-kernel second-kernel source target]
  (app (function/const* 'markov/nnrat-kernel-compose [U])
       element states first-kernel second-kernel source target))
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

;; ((kernel * continuation) * mass) ~ ((mass * kernel) * continuation).
(defn- rotate-three [mass kernel continuation]
  (let [start (rmul (rmul kernel continuation) mass)
        middle (rmul (rmul kernel mass) continuation)
        finish (rmul (rmul mass kernel) continuation)]
    (equivalent-transitive
     start middle finish
     (app (function/const* 'nnrat/multiply-swap-right [])
          kernel continuation mass)
     (multiply-respects
      (rmul kernel mass) (rmul mass kernel)
      continuation continuation
      (app (function/const* 'nnrat/multiply-commutative []) kernel mass)
      (equivalent-reflexive continuation)))))

(def kernel-compose-spec
  {:name 'markov/nnrat-kernel-compose
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['source 'S]
     ['target 'S]]
    (map-sum
     'S
     (function/lam
      [['middle 'S]]
      (rmul (app 'first-kernel 'source 'middle)
            (app 'second-kernel 'middle 'target)))
     (enumeration 'S 'states)))})

(def kernel-step-preserves-total-mass-spec
  {:name 'markov/nnrat-kernel-step-preserves-total-mass-equivalence
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['target 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'target)))
     (total-mass 'S 'states 'mass)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['normalized (kernel-normalized 'S 'states 'kernel)]]
    (let [items (enumeration 'S 'states)
          flow
          (function/lam
           [['target 'S]]
           (function/lam
            [['source 'S]]
            (rmul (app 'mass 'source)
                  (app 'kernel 'source 'target))))
          source-total
          (function/lam
           [['source 'S]]
           (map-sum
            'S
            (function/lam
             [['target 'S]]
             (rmul (app 'mass 'source)
                   (app 'kernel 'source 'target)))
            items))
          swapped-total (map-sum 'S source-total items)
          swap-proof (sum-swap 'S 'S flow items items)
          collapse-source
          (function/lam
           [['source 'S]]
           (let [mass-at-source (app 'mass 'source)
                 kernel-row (app 'kernel 'source)
                 mass-first
                 (function/lam
                  [['target 'S]]
                  (rmul mass-at-source (app kernel-row 'target)))
                 mass-last
                 (function/lam
                  [['target 'S]]
                  (rmul (app kernel-row 'target) mass-at-source))
                 left-sum (map-sum 'S mass-first items)
                 right-sum (map-sum 'S mass-last items)
                 row-total (total-mass 'S 'states kernel-row)
                 scaled-row (rmul row-total mass-at-source)
                 scaled-one (rmul nnrat-one mass-at-source)
                 commute
                 (map-sum-respects
                  'S mass-first mass-last
                  (function/lam
                   [['target 'S]]
                   (app (function/const* 'nnrat/multiply-commutative [])
                        mass-at-source (app kernel-row 'target)))
                  items)
                 factor
                 (equivalent-symmetric
                  scaled-row right-sum
                  (scale-right 'S kernel-row mass-at-source items))
                 normalize-product
                 (multiply-respects
                  row-total nnrat-one
                  mass-at-source mass-at-source
                  (app 'normalized 'source)
                  (equivalent-reflexive mass-at-source))
                 remove-one
                 (app (function/const* 'nnrat/multiply-one-left [])
                      mass-at-source)]
             (equivalent-transitive
              left-sum right-sum mass-at-source commute
              (equivalent-transitive
               right-sum scaled-row mass-at-source factor
               (equivalent-transitive
                scaled-row scaled-one mass-at-source
                normalize-product remove-one)))))
          collapse
          (map-sum-respects 'S source-total 'mass collapse-source items)]
      (equivalent-transitive
       (total-mass
        'S 'states
        (function/lam
         [['target 'S]]
         (kernel-step 'S 'states 'kernel 'mass 'target)))
       swapped-total
       (total-mass 'S 'states 'mass)
       swap-proof collapse)))})

(def kernel-step-preserves-normalization-spec
  {:name 'markov/nnrat-kernel-step-preserves-normalization
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['target 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'target)))
     nnrat-one))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]]
    (equivalent-transitive
     (total-mass
      'S 'states
      (function/lam
       [['target 'S]]
       (kernel-step 'S 'states 'kernel 'mass 'target)))
     (total-mass 'S 'states 'mass)
     nnrat-one
     (app
      (function/const*
       'markov/nnrat-kernel-step-preserves-total-mass-equivalence [U])
      'S 'states 'kernel 'mass 'kernel-normalized)
     'mass-normalized))})

(def kernel-step-compose-spec
  {:name 'markov/nnrat-kernel-step-compose
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]]
    (function/forall
     [['target 'S]]
     (req
      (kernel-step
       'S 'states
       (function/lam
        [['source 'S] ['destination 'S]]
        (kernel-compose
         'S 'states 'first-kernel 'second-kernel 'source 'destination))
       'mass 'target)
      (kernel-step
       'S 'states 'second-kernel
       (function/lam
        [['middle 'S]]
        (kernel-step 'S 'states 'first-kernel 'mass 'middle))
       'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]]
    (function/lam
     [['target 'S]]
     (let [items (enumeration 'S 'states)
           left-map
           (function/lam
            [['source 'S]]
            (rmul
             (app 'mass 'source)
             (map-sum
              'S
              (function/lam
               [['middle 'S]]
               (rmul (app 'first-kernel 'source 'middle)
                     (app 'second-kernel 'middle 'target)))
              items)))
           ordered-inner
           (fn [source]
             (function/lam
              [['middle 'S]]
              (rmul
               (rmul (app 'mass source)
                     (app 'first-kernel source 'middle))
               (app 'second-kernel 'middle 'target))))
           ordered-map
           (function/lam
            [['source 'S]]
            (map-sum 'S (ordered-inner 'source) items))
           expanded (map-sum 'S ordered-map items)
           expand-source
           (function/lam
            [['source 'S]]
            (let [mass-at-source (app 'mass 'source)
                  path
                  (function/lam
                   [['middle 'S]]
                   (rmul (app 'first-kernel 'source 'middle)
                         (app 'second-kernel 'middle 'target)))
                  path-total (map-sum 'S path items)
                  scaled-path (rmul path-total mass-at-source)
                  scaled-map
                  (function/lam
                   [['middle 'S]]
                   (rmul (app path 'middle) mass-at-source))
                  scaled-sum (map-sum 'S scaled-map items)
                  ordered-sum (map-sum 'S (ordered-inner 'source) items)
                  commute-total
                  (app (function/const* 'nnrat/multiply-commutative [])
                       mass-at-source path-total)
                  distribute
                  (scale-right 'S path mass-at-source items)
                  reorder-sum
                  (map-sum-respects
                   'S scaled-map (ordered-inner 'source)
                   (function/lam
                    [['middle 'S]]
                    (rotate-three
                     mass-at-source
                     (app 'first-kernel 'source 'middle)
                     (app 'second-kernel 'middle 'target)))
                   items)]
              (equivalent-transitive
               (rmul mass-at-source path-total)
               scaled-path ordered-sum commute-total
               (equivalent-transitive
                scaled-path scaled-sum ordered-sum
                distribute reorder-sum))))
           expand-all
           (map-sum-respects 'S left-map ordered-map expand-source items)
           flow
           (function/lam
            [['source 'S]]
            (ordered-inner 'source))
           swapped-inner
           (fn [middle]
             (function/lam
              [['source 'S]]
              (rmul
               (rmul (app 'mass 'source)
                     (app 'first-kernel 'source middle))
               (app 'second-kernel middle 'target))))
           swapped-map
           (function/lam
            [['middle 'S]]
            (map-sum 'S (swapped-inner 'middle) items))
           swapped (map-sum 'S swapped-map items)
           swap-proof (sum-swap 'S 'S flow items items)
           right-map
           (function/lam
            [['middle 'S]]
            (rmul
             (kernel-step 'S 'states 'first-kernel 'mass 'middle)
             (app 'second-kernel 'middle 'target)))
           factor-middle
           (function/lam
            [['middle 'S]]
            (equivalent-symmetric
             (app right-map 'middle)
             (app swapped-map 'middle)
             (scale-right
              'S
              (function/lam
               [['source 'S]]
               (rmul (app 'mass 'source)
                     (app 'first-kernel 'source 'middle)))
              (app 'second-kernel 'middle 'target)
              items)))
           factor-all
           (map-sum-respects 'S swapped-map right-map factor-middle items)]
       (equivalent-transitive
        (kernel-step
         'S 'states
         (function/lam
          [['source 'S] ['destination 'S]]
          (kernel-compose
           'S 'states 'first-kernel 'second-kernel 'source 'destination))
         'mass 'target)
        expanded
        (kernel-step
         'S 'states 'second-kernel
         (function/lam
          [['middle 'S]]
          (kernel-step 'S 'states 'first-kernel 'mass 'middle))
         'target)
        expand-all
        (equivalent-transitive
         expanded swapped
         (kernel-step
          'S 'states 'second-kernel
          (function/lam
           [['middle 'S]]
           (kernel-step 'S 'states 'first-kernel 'mass 'middle))
          'target)
         swap-proof factor-all)))))})

(def kernel-compose-rows-normalized-spec
  {:name 'markov/nnrat-kernel-compose-rows-normalized
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['first-normalized
      (kernel-normalized 'S 'states 'first-kernel)]
     ['second-normalized
      (kernel-normalized 'S 'states 'second-kernel)]]
    (kernel-normalized
     'S 'states
     (function/lam
      [['source 'S] ['target 'S]]
      (kernel-compose
       'S 'states 'first-kernel 'second-kernel 'source 'target))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['first-normalized
      (kernel-normalized 'S 'states 'first-kernel)]
     ['second-normalized
      (kernel-normalized 'S 'states 'second-kernel)]]
    (function/lam
     [['source 'S]]
     (equivalent-transitive
      (total-mass
       'S 'states
       (function/lam
        [['target 'S]]
        (kernel-compose
         'S 'states 'first-kernel 'second-kernel 'source 'target)))
      (total-mass 'S 'states (app 'first-kernel 'source))
      nnrat-one
      (app
       (function/const*
        'markov/nnrat-kernel-step-preserves-total-mass-equivalence [U])
       'S 'states 'second-kernel (app 'first-kernel 'source)
       'second-normalized)
      (app 'first-normalized 'source))))})

(def common-stationary-under-compose-spec
  {:name 'markov/nnrat-common-stationary-under-kernel-compose
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['first-fixed
      (stationary 'S 'states 'first-kernel 'mass)]
     ['second-fixed
      (stationary 'S 'states 'second-kernel 'mass)]]
    (stationary
     'S 'states
     (function/lam
      [['source 'S] ['target 'S]]
      (kernel-compose
       'S 'states 'first-kernel 'second-kernel 'source 'target))
     'mass))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['first-kernel (function/arrow 'S 'S nnrat)]
     ['second-kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['first-fixed
      (stationary 'S 'states 'first-kernel 'mass)]
     ['second-fixed
      (stationary 'S 'states 'second-kernel 'mass)]]
    (function/lam
     [['target 'S]]
     (let [first-step
           (function/lam
            [['middle 'S]]
            (kernel-step 'S 'states 'first-kernel 'mass 'middle))
           composed-step
           (kernel-step
            'S 'states
            (function/lam
             [['source 'S] ['destination 'S]]
             (kernel-compose
              'S 'states 'first-kernel 'second-kernel
              'source 'destination))
            'mass 'target)
           iterated-step
           (kernel-step 'S 'states 'second-kernel first-step 'target)
           ordinary-step
           (kernel-step 'S 'states 'second-kernel 'mass 'target)
           compose-proof
           (app (function/const* 'markov/nnrat-kernel-step-compose [U])
                'S 'states 'first-kernel 'second-kernel 'mass 'target)
           transport-first
           (app
            (function/const*
             'markov/nnrat-kernel-step-respects-mass-equivalence [U])
            'S 'states 'second-kernel first-step 'mass
            'first-fixed 'target)]
       (equivalent-transitive
        composed-step iterated-step (app 'mass 'target)
        compose-proof
        (equivalent-transitive
         iterated-step ordinary-step (app 'mass 'target)
         transport-first (app 'second-fixed 'target))))))})

(def definition-specs [kernel-compose-spec])

(def theorem-specs
  [kernel-step-preserves-total-mass-spec
   kernel-step-preserves-normalization-spec
   kernel-step-compose-spec
   kernel-compose-rows-normalized-spec
   common-stationary-under-compose-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-stationarity])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/map-sum-swap :nnrat-fubini fubini/map-sum-swap-spec) (extend-spec-if-missing 'nnrat/multiply-associative :nnrat-product-reassociation reassociation/multiply-associative-spec) (extend-spec-if-missing 'nnrat/multiply-swap-right :nnrat-product-reassociation reassociation/multiply-swap-right-spec) (support/extend-with :finite-markov-kernel-composition (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-kernel-composition))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
