(ns rainbow.math.finite.markov-cesaro
  "Finite Cesaro occupation sums and averages for exact NNRAT Markov dynamics.

  Horizon n contains the n+1 masses mu, mu K, ..., mu K^n.  The average takes
  an explicit exact weight; requiring count(n)*weight ~ 1 states precisely that
  the weight is the reciprocal sample count, without hiding a positivity side
  condition.  A normalized kernel and mass give a normalized average, while a
  stationary mass is fixed by every finite Cesaro average.  Native,
  kernel-checked, and axiom-free on D63."
  (:require [rainbow.math.finite.markov-iteration :as iteration]
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
(defn- succ [value] (app (function/const* 'data/succ []) value))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- total-mass [element states mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element states mass))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- kernel-iterate [element states kernel steps mass state]
  (app (function/const* 'markov/nnrat-kernel-iterate [U])
       element states kernel steps mass state))
(defn- stationary [element states kernel mass]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel mass))
(defn- cesaro-count [steps]
  (app (function/const* 'markov/nnrat-cesaro-count []) steps))
(defn- cesaro-sum [element states kernel steps mass state]
  (app (function/const* 'markov/nnrat-cesaro-sum [U])
       element states kernel steps mass state))
(defn- cesaro-average [element states kernel steps mass weight state]
  (app (function/const* 'markov/nnrat-cesaro-average [U])
       element states kernel steps mass weight state))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric []) left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- add-respects [left equivalent-left right equivalent-right same-left same-right]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left equivalent-left right equivalent-right same-left same-right))
(defn- multiply-respects
  [left equivalent-left right equivalent-right same-left same-right]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       left equivalent-left right equivalent-right same-left same-right))
(defn- map-sum-respects [element left right pointwise items]
  (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
       element left right pointwise items))
(defn- prop-nat-rec [motive base step steps]
  (app (function/const* 'data/Nat.rec [zero-level])
       motive base step steps))

(def cesaro-count-spec
  {:name 'markov/nnrat-cesaro-count
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nnrat)
   :value
   (function/lam
    [['steps nat]]
    (app
     (function/const* 'data/Nat.rec [[:succ zero-level]])
     (function/lam [['ignored nat]] nnrat)
     nnrat-one
     (function/lam
      [['ignored-step nat] ['previous nnrat]]
      (radd 'previous nnrat-one))
     'steps))})

(def cesaro-sum-spec
  {:name 'markov/nnrat-cesaro-sum
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
      [['previous-step nat]
       ['previous-sum (function/arrow 'S nnrat)]]
      (function/lam
       [['state 'S]]
       (radd
        (app 'previous-sum 'state)
        (kernel-iterate
         'S 'states 'kernel (succ 'previous-step) 'mass 'state))))
     'steps))})

(def cesaro-average-spec
  {:name 'markov/nnrat-cesaro-average
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['weight nnrat]]
    (function/arrow 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['weight nnrat]
     ['state 'S]]
    (rmul
     (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)
     'weight))})

(def cesaro-count-zero-spec
  {:name 'markov/nnrat-cesaro-count-zero
   :universes []
   :type (req (cesaro-count zero-nat) nnrat-one)
   :value (equivalent-reflexive nnrat-one)})

(def cesaro-count-successor-spec
  {:name 'markov/nnrat-cesaro-count-successor
   :universes []
   :type
   (function/forall
    [['steps nat]]
    (req (cesaro-count (succ 'steps))
         (radd (cesaro-count 'steps) nnrat-one)))
   :value
   (function/lam
    [['steps nat]]
    (equivalent-reflexive
     (radd (cesaro-count 'steps) nnrat-one)))})

(def cesaro-sum-zero-spec
  {:name 'markov/nnrat-cesaro-sum-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (req
     (cesaro-sum 'S 'states 'kernel zero-nat 'mass 'state)
     (app 'mass 'state)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (equivalent-reflexive (app 'mass 'state)))})

(def cesaro-sum-successor-spec
  {:name 'markov/nnrat-cesaro-sum-successor
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (req
     (cesaro-sum 'S 'states 'kernel (succ 'steps) 'mass 'state)
     (radd
      (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)
      (kernel-iterate
       'S 'states 'kernel (succ 'steps) 'mass 'state))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['steps nat]
     ['mass (function/arrow 'S nnrat)]
     ['state 'S]]
    (equivalent-reflexive
     (radd
      (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)
      (kernel-iterate
       'S 'states 'kernel (succ 'steps) 'mass 'state))))})

(def cesaro-sum-total-mass-spec
  {:name 'markov/nnrat-cesaro-sum-total-mass
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
       (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)))
     (cesaro-count 'steps)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['steps nat]]
    (let [items (enumeration 'S 'states)
          sum-at
          (fn [n]
            (function/lam
             [['state 'S]]
             (cesaro-sum 'S 'states 'kernel n 'mass 'state)))
          iterate-at
          (fn [n]
            (function/lam
             [['state 'S]]
             (kernel-iterate 'S 'states 'kernel n 'mass 'state)))
          motive
          (function/lam
           [['n nat]]
           (req (total-mass 'S 'states (sum-at 'n))
                (cesaro-count 'n)))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (let [previous (sum-at 'n)
                 next-iterate (iterate-at (succ 'n))
                 combined
                 (function/lam
                  [['state 'S]]
                  (radd (app previous 'state)
                        (app next-iterate 'state)))
                 previous-total (total-mass 'S 'states previous)
                 iterate-total (total-mass 'S 'states next-iterate)
                 split
                 (app (function/const* 'nnrat/map-sum-add [U])
                      'S previous next-iterate items)
                 normalized-iterate
                 (app
                  (function/const*
                   'markov/nnrat-kernel-iterate-preserves-normalization [U])
                  'S 'states 'kernel 'mass
                  'kernel-normalized 'mass-normalized (succ 'n))
                 combine
                 (add-respects
                  previous-total (cesaro-count 'n)
                  iterate-total nnrat-one
                  'ih normalized-iterate)]
             (equivalent-transitive
              (total-mass 'S 'states combined)
              (radd previous-total iterate-total)
              (cesaro-count (succ 'n))
              split combine)))]
      (prop-nat-rec motive 'mass-normalized step 'steps)))})

(def cesaro-average-normalized-spec
  {:name 'markov/nnrat-cesaro-average-normalized
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]]
    (req
     (total-mass
      'S 'states
      (function/lam
       [['state 'S]]
       (cesaro-average
        'S 'states 'kernel 'steps 'mass 'weight 'state)))
     nnrat-one))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['mass-normalized (req (total-mass 'S 'states 'mass) nnrat-one)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]]
    (let [items (enumeration 'S 'states)
          sum-mass
          (function/lam
           [['state 'S]]
           (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state))
          average-mass
          (function/lam
           [['state 'S]]
           (cesaro-average
            'S 'states 'kernel 'steps 'mass 'weight 'state))
          sum-total (total-mass 'S 'states sum-mass)
          average-total (total-mass 'S 'states average-mass)
          scaled-total (rmul sum-total 'weight)
          factor
          (equivalent-symmetric
           scaled-total average-total
           (app (function/const* 'nnrat/map-sum-scale-right [U])
                'S sum-mass 'weight items))
          sum-count
          (app (function/const* 'markov/nnrat-cesaro-sum-total-mass [U])
               'S 'states 'kernel 'mass
               'kernel-normalized 'mass-normalized 'steps)
          replace-sum
          (multiply-respects
           sum-total (cesaro-count 'steps)
           'weight 'weight sum-count (equivalent-reflexive 'weight))]
      (equivalent-transitive
       average-total scaled-total nnrat-one factor
       (equivalent-transitive
        scaled-total (rmul (cesaro-count 'steps) 'weight) nnrat-one
        replace-sum 'weight-normalized))))})

(def stationary-cesaro-sum-spec
  {:name 'markov/nnrat-stationary-cesaro-sum
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
      (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)
      (rmul (cesaro-count 'steps) (app 'mass 'state)))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]]
    (let [motive
          (function/lam
           [['n nat]]
           (function/forall
            [['state 'S]]
            (req
             (cesaro-sum 'S 'states 'kernel 'n 'mass 'state)
             (rmul (cesaro-count 'n) (app 'mass 'state)))))
          base
          (function/lam
           [['state 'S]]
           (equivalent-symmetric
            (rmul nnrat-one (app 'mass 'state))
            (app 'mass 'state)
            (app (function/const* 'nnrat/multiply-one-left [])
                 (app 'mass 'state))))
          step
          (function/lam
           [['n nat] ['ih (app motive 'n)]]
           (function/lam
            [['state 'S]]
            (let [mass-at-state (app 'mass 'state)
                  previous-sum
                  (cesaro-sum 'S 'states 'kernel 'n 'mass 'state)
                  next-iterate
                  (kernel-iterate
                   'S 'states 'kernel (succ 'n) 'mass 'state)
                  counted (rmul (cesaro-count 'n) mass-at-state)
                  one-mass (rmul nnrat-one mass-at-state)
                  stationary-iterate
                  (app
                   (function/const* 'markov/nnrat-stationary-kernel-iterate [U])
                   'S 'states 'kernel 'mass 'fixed (succ 'n) 'state)
                  replace-pieces
                  (add-respects
                   previous-sum counted
                   next-iterate mass-at-state
                   (app 'ih 'state) stationary-iterate)
                  introduce-one
                  (add-respects
                   counted counted mass-at-state one-mass
                   (equivalent-reflexive counted)
                   (equivalent-symmetric
                    one-mass mass-at-state
                    (app (function/const* 'nnrat/multiply-one-left [])
                         mass-at-state)))
                  factor
                  (equivalent-symmetric
                   (rmul (radd (cesaro-count 'n) nnrat-one) mass-at-state)
                   (radd counted one-mass)
                   (app
                    (function/const* 'nnrat/multiply-distributes-add-right [])
                    (cesaro-count 'n) nnrat-one mass-at-state))]
              (equivalent-transitive
               (radd previous-sum next-iterate)
               (radd counted mass-at-state)
               (rmul (cesaro-count (succ 'n)) mass-at-state)
               replace-pieces
               (equivalent-transitive
                (radd counted mass-at-state)
                (radd counted one-mass)
                (rmul (radd (cesaro-count 'n) nnrat-one) mass-at-state)
                introduce-one factor)))))]
      (prop-nat-rec motive base step 'steps)))})

(def stationary-cesaro-average-spec
  {:name 'markov/nnrat-stationary-cesaro-average
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]]
    (function/forall
     [['state 'S]]
     (req
      (cesaro-average
       'S 'states 'kernel 'steps 'mass 'weight 'state)
      (app 'mass 'state))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['mass (function/arrow 'S nnrat)]
     ['fixed (stationary 'S 'states 'kernel 'mass)]
     ['steps nat]
     ['weight nnrat]
     ['weight-normalized
      (req (rmul (cesaro-count 'steps) 'weight) nnrat-one)]]
    (function/lam
     [['state 'S]]
     (let [mass-at-state (app 'mass 'state)
           sum-at-state
           (cesaro-sum 'S 'states 'kernel 'steps 'mass 'state)
           count-times-mass
           (rmul (cesaro-count 'steps) mass-at-state)
           average-at-state (rmul sum-at-state 'weight)
           counted-average (rmul count-times-mass 'weight)
           normalized-count-mass
           (rmul (rmul (cesaro-count 'steps) 'weight) mass-at-state)
           replace-sum
           (multiply-respects
            sum-at-state count-times-mass
            'weight 'weight
            (app
             (function/const* 'markov/nnrat-stationary-cesaro-sum [U])
             'S 'states 'kernel 'mass 'fixed 'steps 'state)
            (equivalent-reflexive 'weight))
           reorder
           (app (function/const* 'nnrat/multiply-swap-right [])
                (cesaro-count 'steps) mass-at-state 'weight)
           normalize-product
           (multiply-respects
            (rmul (cesaro-count 'steps) 'weight) nnrat-one
            mass-at-state mass-at-state
            'weight-normalized (equivalent-reflexive mass-at-state))
           remove-one
           (app (function/const* 'nnrat/multiply-one-left []) mass-at-state)]
       (equivalent-transitive
        average-at-state counted-average mass-at-state replace-sum
        (equivalent-transitive
         counted-average normalized-count-mass mass-at-state reorder
         (equivalent-transitive
          normalized-count-mass (rmul nnrat-one mass-at-state) mass-at-state
          normalize-product remove-one))))))})

(def definition-specs
  [cesaro-count-spec cesaro-sum-spec cesaro-average-spec])

(def theorem-specs
  [cesaro-count-zero-spec
   cesaro-count-successor-spec
   cesaro-sum-zero-spec
   cesaro-sum-successor-spec
   cesaro-sum-total-mass-spec
   cesaro-average-normalized-spec
   stationary-cesaro-sum-spec
   stationary-cesaro-average-spec])

(defn extend-environment [env]
  (-> env
      iteration/extend-environment
      (support/extend-with
       :finite-markov-cesaro
       (concat definition-specs theorem-specs))))

(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
