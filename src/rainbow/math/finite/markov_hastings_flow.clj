(ns rainbow.math.finite.markov-hastings-flow
  "General, division-free Hastings accepted-flow certificates.

  For a target mass pi and proposal kernel q, the accepted directed flow is

      min(pi(x) q(x,y), pi(y) q(y,x)).

  This quantity is symmetric without division, positivity side conditions, or
  a special case for zero proposal mass.  A candidate Markov kernel realizes
  the Hastings flow when its target-weighted flow is the accepted flow plus an
  explicitly supplied correction.  If that correction is symmetric, the
  realized kernel satisfies detailed balance; if its rows and the target are
  normalized, the target is stationary.

  The exact ratio acceptance min(forward,reverse)/forward realizes that
  accepted flow for every native nonnegative rational, including the
  zero-forward case without using an invalid inverse law at zero.  For a
  normalized finite proposal row, the accepted row is bounded by one and its
  exact rejection mass is the quotient-safe distance from that total to one;
  accepted mass plus rejection mass is exactly one.

  A certified Boolean equality decision constructs the canonical diagonal
  rejection placement.  When its finite carrier is exhaustive, the placement
  has exactly the computed rejection mass in every row, so the resulting
  canonical kernel is normalized, reversible, and stationary under the stated
  target and proposal normalization premises.  This remains a theorem about
  mathematical kernels, not an executable sampler.  Native, kernel-checked,
  and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.nnrat.additive-reassociation :as add-reassociation]
            [rainbow.math.rational.nnrat.diagonal-spike :as diagonal-spike]
            [rainbow.math.rational.nnrat.list-sum :as list-sum]
            [rainbow.math.rational.nnrat.map-sum-additive :as sum-additive]
            [rainbow.math.rational.nnrat.metric-separation :as separation]
            [rainbow.math.rational.nnrat.minmax :as minmax]
            [rainbow.math.rational.nnrat.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.nnrat.ordered-distance :as ordered-distance]
            [rainbow.math.rational.nnrat.order-scale :as order-scale]
            [rainbow.math.rational.nnrat.product-reassociation :as reassociation]
            [rainbow.math.logic.proposition :as proposition]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))
(def bool (function/const* 'data/Bool []))
(def nat (function/const* 'data/Nat []))
(def nat-zero (function/const* 'data/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- carrier-member [element states value]
  (app (function/const* 'list/membership [U])
       element (enumeration element states) value))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- state-equality [element left right]
  (function/equality data-u element left right))
(defn- state-equality-decidable [element]
  (function/forall
   [['left element] ['right element]]
   (proposition/disjunction
    (state-equality element 'left 'right)
    (proposition/negation (state-equality element 'left 'right)))))
(defn- at-most [left right]
  (app (function/const* 'nnrat/at-most []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- rmul [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- rdiv [left right]
  (app (function/const* 'nnrat/divide []) left right))
(defn- rdistance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- reciprocal [value]
  (app (function/const* 'nnrat/reciprocal []) value))
(defn- succ [value]
  (app (function/const* 'data/succ []) value))
(defn- rmake [numerator denominator-predecessor]
  (app (function/const* 'nnrat/make [])
       numerator denominator-predecessor))
(defn- minimum [left right]
  (app (function/const* 'minmax/min []) left right))
(defn- total-mass [element states mass]
  (app (function/const* 'probability/nnrat-total-mass [U])
       element states mass))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [U])
       element states kernel))
(defn- detailed-balance [element target kernel]
  (app (function/const* 'markov/nnrat-detailed-balance [U])
       element target kernel))
(defn- stationary [element states kernel target]
  (app (function/const* 'markov/nnrat-stationary [U])
       element states kernel target))
(defn- accepted-flow [element target proposal left right]
  (app (function/const* 'mcmc/nnrat-hastings-accepted-flow [U])
       element target proposal left right))
(defn- ratio-acceptance [forward reverse]
  (app (function/const* 'mcmc/nnrat-hastings-ratio-acceptance [])
       forward reverse))
(defn- accepted-transition [element target proposal left right]
  (app (function/const* 'mcmc/nnrat-hastings-accepted-transition [U])
       element target proposal left right))
(defn- rejection-mass [element states target proposal left]
  (app (function/const* 'mcmc/nnrat-hastings-rejection-mass [U])
       element states target proposal left))
(defn- completed-kernel [element states target proposal placement]
  (app (function/const* 'mcmc/nnrat-hastings-completed-kernel [U])
       element states target proposal placement))
(defn- rejection-correction [element target placement]
  (app (function/const* 'mcmc/nnrat-hastings-rejection-correction [U])
       element target placement))
(defn- off-diagonal-zero [element placement]
  (app (function/const* 'mcmc/nnrat-off-diagonal-zero [U])
       element placement))
(defn- certified-equality-decision [element decision]
  (app (function/const* 'finite/certified-equality-decision [U])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [U])
       element states decision))
(defn- diagonal-rejection-placement
  [element states target proposal decision]
  (app
   (function/const*
    'mcmc/nnrat-hastings-diagonal-rejection-placement [U])
   element states target proposal decision))
(defn- canonical-kernel [element states target proposal decision]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [U])
       element states target proposal decision))
(defn- symmetric-flow [element flow]
  (app (function/const* 'mcmc/nnrat-symmetric-flow [U]) element flow))
(defn- realization [element target proposal kernel correction]
  (app (function/const* 'mcmc/nnrat-hastings-kernel-realization [U])
       element target proposal kernel correction))
(defn- equivalent-symmetric [left right same]
  (app (function/const* 'nnrat/equivalent-symmetric [])
       left right same))
(defn- equivalent-transitive [left middle right first second]
  (app (function/const* 'nnrat/equivalent-transitive [])
       left middle right first second))
(defn- equivalent-reflexive [value]
  (app (function/const* 'nnrat/equivalent-reflexive []) value))
(defn- add-respects
  [left left-prime right right-prime same-left same-right]
  (app (function/const* 'nnrat/add-respects-equivalence [])
       left left-prime right right-prime same-left same-right))
(defn- multiply-respects
  [left left-prime right right-prime same-left same-right]
  (app (function/const* 'nnrat/multiply-respects-equivalence [])
       left left-prime right right-prime same-left same-right))
(defn- min-left [left right]
  (app (function/const* 'minmax/min-lower-left []) left right))
(defn- min-right [left right]
  (app (function/const* 'minmax/min-lower-right []) left right))
(defn- below-min [lower left right lower-left lower-right]
  (app (function/const* 'minmax/at-most-min [])
       lower left right lower-left lower-right))
(defn- antisymmetric [left right left-right right-left]
  (app (function/const* 'nnrat/at-most-antisymmetric [])
       left right left-right right-left))
(defn- at-most-respects
  [left equivalent-left right equivalent-right
   same-left same-right ordered]
  (app (function/const* 'nnrat/at-most-respects-equivalence [])
       left equivalent-left right equivalent-right
       same-left same-right ordered))
(defn- at-most-transitive [left middle right first second]
  (app (function/const* 'nnrat/at-most-transitive [])
       left middle right first second))
(defn- equivalence-forward [left right iff evidence]
  (app (function/const* 'proposition/equivalence-forward [])
       left right iff evidence))

(def hastings-accepted-flow-spec
  {:name 'mcmc/nnrat-hastings-accepted-flow
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (minimum
     (rmul (app 'target 'left) (app 'proposal 'left 'right))
     (rmul (app 'target 'right) (app 'proposal 'right 'left))))})

(def hastings-ratio-acceptance-spec
  {:name 'mcmc/nnrat-hastings-ratio-acceptance
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nnrat nnrat nnrat)
   :value
   (function/lam
    [['forward nnrat] ['reverse nnrat]]
    (rdiv (minimum 'forward 'reverse) 'forward))})

(def hastings-accepted-transition-spec
  {:name 'mcmc/nnrat-hastings-accepted-transition
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (let [forward
          (rmul (app 'target 'left) (app 'proposal 'left 'right))
          reverse
          (rmul (app 'target 'right) (app 'proposal 'right 'left))]
      (rmul (app 'proposal 'left 'right)
            (ratio-acceptance forward reverse))))})

(def hastings-rejection-mass-spec
  {:name 'mcmc/nnrat-hastings-rejection-mass
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S]]
    (let [accepted-row
          (function/lam
           [['right 'S]]
           (accepted-transition 'S 'target 'proposal 'left 'right))
          accepted-total (total-mass 'S 'states accepted-row)]
      (rdistance accepted-total nnrat-one)))})

(def hastings-completed-kernel-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (radd
     (accepted-transition 'S 'target 'proposal 'left 'right)
     (app 'placement 'left 'right)))})

(def hastings-rejection-correction-spec
  {:name 'mcmc/nnrat-hastings-rejection-correction
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (rmul (app 'target 'left) (app 'placement 'left 'right)))})

(def off-diagonal-zero-spec
  {:name 'mcmc/nnrat-off-diagonal-zero
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['placement (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['placement (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['left 'S] ['right 'S]
      ['different
       (proposition/negation (state-equality 'S 'left 'right))]]
     (req (app 'placement 'left 'right) nnrat-zero)))})

(def hastings-diagonal-rejection-placement-spec
  {:name 'mcmc/nnrat-hastings-diagonal-rejection-placement
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]]
    (let [rejection
          (function/lam
           [['left 'S]]
           (rejection-mass 'S 'states 'target 'proposal 'left))]
      (app (function/const* 'finite/nnrat-diagonal-spike [U])
           'S 'decision rejection)))})

(def hastings-canonical-kernel-spec
  {:name 'mcmc/nnrat-hastings-canonical-kernel
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]]
    (function/arrow 'S 'S nnrat))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]]
    (completed-kernel
     'S 'states 'target 'proposal
     (diagonal-rejection-placement
      'S 'states 'target 'proposal 'decision)))})

(def symmetric-flow-spec
  {:name 'mcmc/nnrat-symmetric-flow
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['flow (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u] ['flow (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['left 'S] ['right 'S]]
     (req (app 'flow 'left 'right)
          (app 'flow 'right 'left))))})

(def hastings-kernel-realization-spec
  {:name 'mcmc/nnrat-hastings-kernel-realization
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]]
    'Prop)
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]]
    (function/forall
     [['left 'S] ['right 'S]]
     (req
      (rmul (app 'target 'left) (app 'kernel 'left 'right))
      (radd (accepted-flow 'S 'target 'proposal 'left 'right)
            (app 'correction 'left 'right)))))})

(def min-commutative-spec
  {:name 'nnrat/min-commutative
   :universes []
   :type
   (function/forall
    [['left nnrat] ['right nnrat]]
    (req (minimum 'left 'right) (minimum 'right 'left)))
   :value
   (function/lam
    [['left nnrat] ['right nnrat]]
    (let [lr (minimum 'left 'right)
          rl (minimum 'right 'left)]
      (antisymmetric
       lr rl
       (below-min lr 'right 'left
                  (min-right 'left 'right)
                  (min-left 'left 'right))
       (below-min rl 'left 'right
                  (min-right 'right 'left)
                  (min-left 'right 'left)))))})

(def hastings-accepted-flow-symmetric-spec
  {:name 'mcmc/nnrat-hastings-accepted-flow-symmetric
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (req (accepted-flow 'S 'target 'proposal 'left 'right)
         (accepted-flow 'S 'target 'proposal 'right 'left)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (app
     (function/const* 'nnrat/min-commutative [])
     (rmul (app 'target 'left) (app 'proposal 'left 'right))
     (rmul (app 'target 'right) (app 'proposal 'right 'left))))})

(def positive-hastings-ratio-realizes-accepted-flow-spec
  {:name 'mcmc/nnrat-positive-hastings-ratio-realizes-accepted-flow
   :universes []
   :type
   (function/forall
    [['numerator-predecessor nat]
     ['denominator-predecessor nat]
     ['reverse nnrat]]
    (let [forward
          (rmake (succ 'numerator-predecessor)
                 'denominator-predecessor)]
      (req
       (rmul forward (ratio-acceptance forward 'reverse))
       (minimum forward 'reverse))))
   :value
   (function/lam
    [['numerator-predecessor nat]
     ['denominator-predecessor nat]
     ['reverse nnrat]]
    (app
     (function/const* 'nnrat/multiply-divide-cancel [])
     'numerator-predecessor 'denominator-predecessor
     (minimum
      (rmake (succ 'numerator-predecessor)
             'denominator-predecessor)
      'reverse)))})

(def zero-hastings-ratio-realizes-accepted-flow-spec
  {:name 'mcmc/nnrat-zero-hastings-ratio-realizes-accepted-flow
   :universes []
   :type
   (function/forall
    [['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake nat-zero 'denominator-predecessor)]
      (req
       (rmul forward (ratio-acceptance forward 'reverse))
       (minimum forward 'reverse))))
   :value
   (function/lam
    [['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake nat-zero 'denominator-predecessor)
          selected (minimum forward 'reverse)
          acceptance (ratio-acceptance forward 'reverse)
          forward-zero
          (app (function/const* 'equality/reflexive [type-level])
               nat nat-zero)
          product-zero
          (equivalent-transitive
           (rmul forward acceptance)
           (rmul nnrat-zero acceptance)
           nnrat-zero
           (multiply-respects
            forward nnrat-zero acceptance acceptance
            forward-zero (equivalent-reflexive acceptance))
           (app (function/const* 'nnrat/multiply-zero-left []) acceptance))
          selected-zero
          (antisymmetric
           selected nnrat-zero
           (at-most-respects
            selected selected nnrat-zero forward
            (equivalent-reflexive selected)
            (equivalent-symmetric forward nnrat-zero forward-zero)
            (min-left forward 'reverse))
           (app (function/const* 'nnrat/zero-at-most []) selected))]
      (equivalent-transitive
       (rmul forward acceptance) nnrat-zero selected
       product-zero
       (equivalent-symmetric selected nnrat-zero selected-zero))))})

(def made-hastings-ratio-realizes-accepted-flow-spec
  {:name 'mcmc/nnrat-made-hastings-ratio-realizes-accepted-flow
   :universes []
   :type
   (function/forall
    [['numerator nat] ['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake 'numerator 'denominator-predecessor)]
      (req
       (rmul forward (ratio-acceptance forward 'reverse))
       (minimum forward 'reverse))))
   :value
   (function/lam
    [['numerator nat] ['denominator-predecessor nat] ['reverse nnrat]]
    (let [motive
          (function/lam
           [['candidate nat]]
           (let [forward (rmake 'candidate 'denominator-predecessor)]
             (req
              (rmul forward (ratio-acceptance forward 'reverse))
              (minimum forward 'reverse))))]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (app
        (function/const*
         'mcmc/nnrat-zero-hastings-ratio-realizes-accepted-flow [])
        'denominator-predecessor 'reverse)
       (function/lam
        [['predecessor nat]
         ['ignored-induction-hypothesis (app motive 'predecessor)]]
        (app
         (function/const*
          'mcmc/nnrat-positive-hastings-ratio-realizes-accepted-flow [])
         'predecessor 'denominator-predecessor 'reverse))
       'numerator)))})

(def hastings-ratio-realizes-accepted-flow-spec
  {:name 'mcmc/nnrat-hastings-ratio-realizes-accepted-flow
   :universes []
   :type
   (function/forall
    [['forward nnrat] ['reverse nnrat]]
    (req
     (rmul 'forward (ratio-acceptance 'forward 'reverse))
     (minimum 'forward 'reverse)))
   :value
   (function/lam
    [['forward nnrat] ['reverse nnrat]]
    (let [motive
          (function/lam
           [['candidate nnrat]]
           (req
            (rmul 'candidate (ratio-acceptance 'candidate 'reverse))
            (minimum 'candidate 'reverse)))]
      (app
       (function/const* 'data/Product.rec
                        [type-level type-level zero-level])
       nat nat motive
       (function/lam
        [['numerator nat] ['denominator-predecessor nat]]
        (app
         (function/const*
          'mcmc/nnrat-made-hastings-ratio-realizes-accepted-flow [])
         'numerator 'denominator-predecessor 'reverse))
       'forward)))})

(def positive-hastings-ratio-acceptance-at-most-one-spec
  {:name 'mcmc/nnrat-positive-hastings-ratio-acceptance-at-most-one
   :universes []
   :type
   (function/forall
    [['numerator-predecessor nat]
     ['denominator-predecessor nat]
     ['reverse nnrat]]
    (let [forward
          (rmake (succ 'numerator-predecessor)
                 'denominator-predecessor)]
      (at-most (ratio-acceptance forward 'reverse) nnrat-one)))
   :value
   (function/lam
    [['numerator-predecessor nat]
     ['denominator-predecessor nat]
     ['reverse nnrat]]
    (let [forward
          (rmake (succ 'numerator-predecessor)
                 'denominator-predecessor)
          selected (minimum forward 'reverse)
          scaled-one (rmul forward nnrat-one)
          selected-at-most-scaled-one
          (at-most-respects
           selected selected scaled-one forward
           (equivalent-reflexive selected)
           (app (function/const* 'nnrat/multiply-one-right []) forward)
           (min-left forward 'reverse))
          normalized
          (app
           (function/const*
            'nnrat/at-most-multiply-left-normalize-lower [])
           'numerator-predecessor 'denominator-predecessor
           selected nnrat-one)]
      (equivalence-forward
       (at-most selected scaled-one)
       (at-most (rdiv selected forward) nnrat-one)
       normalized selected-at-most-scaled-one)))})

(def zero-hastings-ratio-acceptance-at-most-one-spec
  {:name 'mcmc/nnrat-zero-hastings-ratio-acceptance-at-most-one
   :universes []
   :type
   (function/forall
    [['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake nat-zero 'denominator-predecessor)]
      (at-most (ratio-acceptance forward 'reverse) nnrat-one)))
   :value
   (function/lam
    [['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake nat-zero 'denominator-predecessor)
          selected (minimum forward 'reverse)
          inverse (reciprocal forward)
          acceptance (ratio-acceptance forward 'reverse)
          forward-zero
          (app (function/const* 'equality/reflexive [type-level])
               nat nat-zero)
          selected-zero
          (antisymmetric
           selected nnrat-zero
           (at-most-respects
            selected selected nnrat-zero forward
            (equivalent-reflexive selected)
            (equivalent-symmetric forward nnrat-zero forward-zero)
            (min-left forward 'reverse))
           (app (function/const* 'nnrat/zero-at-most []) selected))
          acceptance-zero
          (equivalent-transitive
           acceptance (rmul nnrat-zero inverse) nnrat-zero
           (multiply-respects
            selected nnrat-zero inverse inverse
            selected-zero (equivalent-reflexive inverse))
           (app (function/const* 'nnrat/multiply-zero-left []) inverse))]
      (at-most-respects
       acceptance nnrat-zero nnrat-one nnrat-one
       acceptance-zero (equivalent-reflexive nnrat-one)
       (app (function/const* 'nnrat/zero-at-most []) nnrat-one))))})

(def made-hastings-ratio-acceptance-at-most-one-spec
  {:name 'mcmc/nnrat-made-hastings-ratio-acceptance-at-most-one
   :universes []
   :type
   (function/forall
    [['numerator nat] ['denominator-predecessor nat] ['reverse nnrat]]
    (let [forward (rmake 'numerator 'denominator-predecessor)]
      (at-most (ratio-acceptance forward 'reverse) nnrat-one)))
   :value
   (function/lam
    [['numerator nat] ['denominator-predecessor nat] ['reverse nnrat]]
    (let [motive
          (function/lam
           [['candidate nat]]
           (at-most
            (ratio-acceptance
             (rmake 'candidate 'denominator-predecessor) 'reverse)
            nnrat-one))]
      (app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (app
        (function/const*
         'mcmc/nnrat-zero-hastings-ratio-acceptance-at-most-one [])
        'denominator-predecessor 'reverse)
       (function/lam
        [['predecessor nat]
         ['ignored-induction-hypothesis (app motive 'predecessor)]]
        (app
         (function/const*
          'mcmc/nnrat-positive-hastings-ratio-acceptance-at-most-one [])
         'predecessor 'denominator-predecessor 'reverse))
       'numerator)))})

(def hastings-ratio-acceptance-at-most-one-spec
  {:name 'mcmc/nnrat-hastings-ratio-acceptance-at-most-one
   :universes []
   :type
   (function/forall
    [['forward nnrat] ['reverse nnrat]]
    (at-most (ratio-acceptance 'forward 'reverse) nnrat-one))
   :value
   (function/lam
    [['forward nnrat] ['reverse nnrat]]
    (let [motive
          (function/lam
           [['candidate nnrat]]
           (at-most (ratio-acceptance 'candidate 'reverse) nnrat-one))]
      (app
       (function/const* 'data/Product.rec
                        [type-level type-level zero-level])
       nat nat motive
       (function/lam
        [['numerator nat] ['denominator-predecessor nat]]
        (app
         (function/const*
          'mcmc/nnrat-made-hastings-ratio-acceptance-at-most-one [])
         'numerator 'denominator-predecessor 'reverse))
       'forward)))})

(def hastings-accepted-transition-at-most-proposal-spec
  {:name 'mcmc/nnrat-hastings-accepted-transition-at-most-proposal
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (at-most
     (accepted-transition 'S 'target 'proposal 'left 'right)
     (app 'proposal 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (let [proposal-mass (app 'proposal 'left 'right)
          forward (rmul (app 'target 'left) proposal-mass)
          reverse
          (rmul (app 'target 'right) (app 'proposal 'right 'left))
          acceptance (ratio-acceptance forward reverse)
          accepted (rmul proposal-mass acceptance)
          scaled-one (rmul proposal-mass nnrat-one)
          acceptance-at-most-one
          (app
           (function/const*
            'mcmc/nnrat-hastings-ratio-acceptance-at-most-one [])
           forward reverse)
          scaled
          (app (function/const* 'nnrat/multiply-monotone [])
               proposal-mass acceptance nnrat-one
               acceptance-at-most-one)]
      (at-most-respects
       accepted accepted proposal-mass scaled-one
       (equivalent-reflexive accepted)
       (equivalent-symmetric
        scaled-one proposal-mass
        (app (function/const* 'nnrat/multiply-one-right []) proposal-mass))
       scaled)))})

(def hastings-accepted-transition-realizes-flow-spec
  {:name 'mcmc/nnrat-hastings-accepted-transition-realizes-flow
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (req
     (rmul (app 'target 'left)
           (accepted-transition 'S 'target 'proposal 'left 'right))
     (accepted-flow 'S 'target 'proposal 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]]
    (let [target-mass (app 'target 'left)
          proposal-mass (app 'proposal 'left 'right)
          reverse
          (rmul (app 'target 'right) (app 'proposal 'right 'left))
          forward (rmul target-mass proposal-mass)
          acceptance (ratio-acceptance forward reverse)
          weighted-accepted
          (rmul target-mass (rmul proposal-mass acceptance))
          associated (rmul forward acceptance)]
      (equivalent-transitive
       weighted-accepted associated
       (accepted-flow 'S 'target 'proposal 'left 'right)
       (equivalent-symmetric
        associated weighted-accepted
        (app (function/const* 'nnrat/multiply-associative [])
             target-mass proposal-mass acceptance))
       (app
        (function/const*
         'mcmc/nnrat-hastings-ratio-realizes-accepted-flow [])
        forward reverse))))})

(def hastings-accepted-row-at-most-proposal-row-spec
  {:name 'mcmc/nnrat-hastings-accepted-row-at-most-proposal-row
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S]]
    (at-most
     (total-mass
      'S 'states
      (function/lam
       [['right 'S]]
       (accepted-transition 'S 'target 'proposal 'left 'right)))
     (total-mass 'S 'states (app 'proposal 'left))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S]]
    (let [accepted-row
          (function/lam
           [['right 'S]]
           (accepted-transition 'S 'target 'proposal 'left 'right))
          proposal-row (app 'proposal 'left)]
      (app
       (function/const* 'nnrat/map-sum-monotone [U])
       'S accepted-row proposal-row
       (function/lam
        [['right 'S]]
        (app
         (function/const*
          'mcmc/nnrat-hastings-accepted-transition-at-most-proposal [U])
         'S 'target 'proposal 'left 'right))
       (enumeration 'S 'states))))})

(def hastings-accepted-row-at-most-one-spec
  {:name 'mcmc/nnrat-hastings-accepted-row-at-most-one
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['left 'S]]
    (at-most
     (total-mass
      'S 'states
      (function/lam
       [['right 'S]]
       (accepted-transition 'S 'target 'proposal 'left 'right)))
     nnrat-one))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['left 'S]]
    (let [accepted-row
          (function/lam
           [['right 'S]]
           (accepted-transition 'S 'target 'proposal 'left 'right))
          accepted-total (total-mass 'S 'states accepted-row)
          proposal-total (total-mass 'S 'states (app 'proposal 'left))]
      (at-most-transitive
       accepted-total proposal-total nnrat-one
       (app
        (function/const*
         'mcmc/nnrat-hastings-accepted-row-at-most-proposal-row [U])
        'S 'states 'target 'proposal 'left)
       (app (function/const* 'nnrat/equivalent-to-at-most [])
            proposal-total nnrat-one
            (app 'proposal-normalized 'left)))))})

(def hastings-accepted-row-plus-rejection-is-one-spec
  {:name 'mcmc/nnrat-hastings-accepted-row-plus-rejection-is-one
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['left 'S]]
    (let [accepted-row
          (function/lam
           [['right 'S]]
           (accepted-transition 'S 'target 'proposal 'left 'right))
          accepted-total (total-mass 'S 'states accepted-row)]
      (req
       (radd accepted-total
             (rejection-mass 'S 'states 'target 'proposal 'left))
       nnrat-one)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['left 'S]]
    (let [accepted-row
          (function/lam
           [['right 'S]]
           (accepted-transition 'S 'target 'proposal 'left 'right))
          accepted-total (total-mass 'S 'states accepted-row)]
      (app
       (function/const* 'nnrat/add-distance-of-at-most [])
       accepted-total nnrat-one
       (app
        (function/const*
         'mcmc/nnrat-hastings-accepted-row-at-most-one [U])
        'S 'states 'target 'proposal 'proposal-normalized 'left))))})

(def hastings-completed-kernel-rows-normalized-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-rows-normalized
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]]
    (kernel-normalized
     'S 'states
     (completed-kernel 'S 'states 'target 'proposal 'placement)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]]
    (function/lam
     [['left 'S]]
     (let [accepted-row
           (function/lam
            [['right 'S]]
            (accepted-transition 'S 'target 'proposal 'left 'right))
           placement-row (app 'placement 'left)
           accepted-total (total-mass 'S 'states accepted-row)
           placement-total (total-mass 'S 'states placement-row)
           rejection (rejection-mass 'S 'states 'target 'proposal 'left)
           completed-total
           (total-mass
            'S 'states
            (app
             (completed-kernel 'S 'states 'target 'proposal 'placement)
             'left))
           split
           (app (function/const* 'nnrat/map-sum-add [U])
                'S accepted-row placement-row (enumeration 'S 'states))
           replace-placement
           (add-respects
            accepted-total accepted-total placement-total rejection
            (equivalent-reflexive accepted-total)
            (app 'placement-has-rejection-mass 'left))]
       (equivalent-transitive
        completed-total (radd accepted-total placement-total) nnrat-one
        split
        (equivalent-transitive
         (radd accepted-total placement-total)
         (radd accepted-total rejection) nnrat-one
         replace-placement
         (app
          (function/const*
           'mcmc/nnrat-hastings-accepted-row-plus-rejection-is-one [U])
          'S 'states 'target 'proposal 'proposal-normalized 'left))))))})

(def hastings-completed-kernel-realization-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-realization
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]]
    (realization
     'S 'target 'proposal
     (completed-kernel 'S 'states 'target 'proposal 'placement)
     (rejection-correction 'S 'target 'placement)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]]
    (function/lam
     [['left 'S] ['right 'S]]
     (let [target-mass (app 'target 'left)
           accepted
           (accepted-transition 'S 'target 'proposal 'left 'right)
           placed (app 'placement 'left 'right)
           accepted-flow-value
           (accepted-flow 'S 'target 'proposal 'left 'right)
           correction-value
           (app (rejection-correction 'S 'target 'placement)
                'left 'right)
           distributed
           (app (function/const* 'nnrat/multiply-distributes-add-left [])
                target-mass accepted placed)
           replace-accepted
           (add-respects
            (rmul target-mass accepted) accepted-flow-value
            correction-value correction-value
            (app
             (function/const*
              'mcmc/nnrat-hastings-accepted-transition-realizes-flow [U])
             'S 'target 'proposal 'left 'right)
            (equivalent-reflexive correction-value))]
       (equivalent-transitive
        (rmul target-mass (radd accepted placed))
        (radd (rmul target-mass accepted) correction-value)
        (radd accepted-flow-value correction-value)
        distributed replace-accepted))))})

(def hastings-rejection-correction-symmetric-of-off-diagonal-zero-spec
  {:name 'mcmc/nnrat-hastings-rejection-correction-symmetric-of-off-diagonal-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['equality-decidable (state-equality-decidable 'S)]
     ['off-diagonal (off-diagonal-zero 'S 'placement)]]
    (symmetric-flow
     'S (rejection-correction 'S 'target 'placement)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['equality-decidable (state-equality-decidable 'S)]
     ['off-diagonal (off-diagonal-zero 'S 'placement)]]
    (function/lam
     [['left 'S] ['right 'S]]
     (let [same (state-equality 'S 'left 'right)
           different (proposition/negation same)
           left-target (app 'target 'left)
           right-target (app 'target 'right)
           left-placement (app 'placement 'left 'right)
           right-placement (app 'placement 'right 'left)
           left-product (rmul left-target left-placement)
           right-product (rmul right-target right-placement)
           goal (req left-product right-product)]
       (app
        (function/const* 'proposition/use-disjunction [])
        same different goal
        (app 'equality-decidable 'left 'right)
        (function/lam
         [['same-state same]]
         (app
          (function/const* 'equality/substitution [data-u])
          'S 'left 'right 'same-state
          (function/lam
           [['candidate 'S]]
           (req
            (rmul left-target (app 'placement 'left 'candidate))
            (rmul (app 'target 'candidate)
                  (app 'placement 'candidate 'left))))
          (equivalent-reflexive
           (rmul left-target (app 'placement 'left 'left)))))
        (function/lam
         [['different-state different]]
         (let [reverse-different
               (function/lam
                [['same-reversed (state-equality 'S 'right 'left)]]
                (app
                 'different-state
                 (app (function/const* 'equality/symmetric [data-u])
                      'S 'right 'left 'same-reversed)))
               left-placement-zero
               (app 'off-diagonal 'left 'right 'different-state)
               right-placement-zero
               (app 'off-diagonal 'right 'left reverse-different)
               left-to-scaled-zero
               (multiply-respects
                left-target left-target left-placement nnrat-zero
                (equivalent-reflexive left-target) left-placement-zero)
               right-to-scaled-zero
               (multiply-respects
                right-target right-target right-placement nnrat-zero
                (equivalent-reflexive right-target) right-placement-zero)
               left-to-zero
               (equivalent-transitive
                left-product (rmul left-target nnrat-zero) nnrat-zero
                left-to-scaled-zero
                (app (function/const* 'nnrat/multiply-zero-right [])
                     left-target))
               right-to-zero
               (equivalent-transitive
                right-product (rmul right-target nnrat-zero) nnrat-zero
                right-to-scaled-zero
                (app (function/const* 'nnrat/multiply-zero-right [])
                     right-target))]
           (equivalent-transitive
            left-product nnrat-zero right-product left-to-zero
            (equivalent-symmetric
             right-product nnrat-zero right-to-zero))))))))})

(def hastings-completed-kernel-detailed-balance-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-detailed-balance
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['weighted-placement-symmetric
      (symmetric-flow
       'S (rejection-correction 'S 'target 'placement))]]
    (detailed-balance
     'S 'target
     (completed-kernel 'S 'states 'target 'proposal 'placement)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['weighted-placement-symmetric
      (symmetric-flow
       'S (rejection-correction 'S 'target 'placement))]]
    (app
     (function/const*
      'mcmc/nnrat-hastings-realization-detailed-balance [U])
     'S 'target 'proposal
     (completed-kernel 'S 'states 'target 'proposal 'placement)
     (rejection-correction 'S 'target 'placement)
     (app
      (function/const*
       'mcmc/nnrat-hastings-completed-kernel-realization [U])
      'S 'states 'target 'proposal 'placement)
     'weighted-placement-symmetric))})

(def hastings-completed-kernel-stationary-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-stationary
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]
     ['weighted-placement-symmetric
      (symmetric-flow
       'S (rejection-correction 'S 'target 'placement))]]
    (stationary
     'S 'states
     (completed-kernel 'S 'states 'target 'proposal 'placement)
     'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]
     ['weighted-placement-symmetric
      (symmetric-flow
       'S (rejection-correction 'S 'target 'placement))]]
    (app
     (function/const* 'markov/nnrat-detailed-balance-implies-stationary [U])
     'S 'states
     (completed-kernel 'S 'states 'target 'proposal 'placement)
     'target
     (app
      (function/const*
       'mcmc/nnrat-hastings-completed-kernel-rows-normalized [U])
      'S 'states 'target 'proposal 'placement
      'proposal-normalized 'placement-has-rejection-mass)
     (app
      (function/const*
       'mcmc/nnrat-hastings-completed-kernel-detailed-balance [U])
      'S 'states 'target 'proposal 'placement
      'weighted-placement-symmetric)))})

(def hastings-completed-kernel-stationary-of-off-diagonal-zero-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-stationary-of-off-diagonal-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['equality-decidable (state-equality-decidable 'S)]
     ['off-diagonal (off-diagonal-zero 'S 'placement)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]]
    (stationary
     'S 'states
     (completed-kernel 'S 'states 'target 'proposal 'placement)
     'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['equality-decidable (state-equality-decidable 'S)]
     ['off-diagonal (off-diagonal-zero 'S 'placement)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]
     ['placement-has-rejection-mass
      (function/forall
       [['left 'S]]
       (req
        (total-mass 'S 'states (app 'placement 'left))
        (rejection-mass 'S 'states 'target 'proposal 'left)))]]
    (app
     (function/const*
      'mcmc/nnrat-hastings-completed-kernel-stationary [U])
     'S 'states 'target 'proposal 'placement
     'target-normalized 'proposal-normalized
     'placement-has-rejection-mass
     (app
      (function/const*
       'mcmc/nnrat-hastings-rejection-correction-symmetric-of-off-diagonal-zero
       [U])
      'S 'target 'placement 'equality-decidable 'off-diagonal)))})

(def hastings-diagonal-rejection-placement-off-diagonal-zero-spec
  {:name 'mcmc/nnrat-hastings-diagonal-rejection-placement-off-diagonal-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality-decision 'S 'decision)]]
    (off-diagonal-zero
     'S
     (diagonal-rejection-placement
      'S 'states 'target 'proposal 'decision)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified
      (certified-equality-decision 'S 'decision)]]
    (function/lam
     [['left 'S] ['right 'S]
      ['different
       (proposition/negation (state-equality 'S 'left 'right))]]
     (let [rejection
           (function/lam
            [['state 'S]]
            (rejection-mass 'S 'states 'target 'proposal 'state))]
       (app
        (function/const*
         'finite/nnrat-diagonal-spike-zero-of-different [U])
        'S 'decision rejection 'certified
        'left 'right 'different))))})

(def hastings-diagonal-rejection-placement-has-rejection-mass-spec
  {:name 'mcmc/nnrat-hastings-diagonal-rejection-placement-has-rejection-mass
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality-decision 'S 'decision)]
     ['carrier-covered
      (function/forall
       [['state 'S]] (carrier-member 'S 'states 'state))]]
    (function/forall
     [['left 'S]]
     (req
      (total-mass
       'S 'states
       (app
        (diagonal-rejection-placement
         'S 'states 'target 'proposal 'decision)
        'left))
      (rejection-mass 'S 'states 'target 'proposal 'left))))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality-decision 'S 'decision)]
     ['carrier-covered
      (function/forall
       [['state 'S]] (carrier-member 'S 'states 'state))]]
    (function/lam
     [['left 'S]]
     (let [rejection
           (function/lam
            [['state 'S]]
            (rejection-mass 'S 'states 'target 'proposal 'state))]
       (app
        (function/const* 'finite/nnrat-finset-diagonal-spike-total [U])
        'S 'states 'decision rejection 'certified
        'left (app 'carrier-covered 'left)))))})

(def hastings-canonical-kernel-stationary-spec
  {:name 'mcmc/nnrat-hastings-canonical-kernel-stationary
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality-decision 'S 'decision)]
     ['carrier-covered
      (function/forall
       [['state 'S]] (carrier-member 'S 'states 'state))]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]]
    (stationary
     'S 'states
     (canonical-kernel 'S 'states 'target 'proposal 'decision)
     'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['certified (certified-equality-decision 'S 'decision)]
     ['carrier-covered
      (function/forall
       [['state 'S]] (carrier-member 'S 'states 'state))]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]]
    (let [placement
          (diagonal-rejection-placement
           'S 'states 'target 'proposal 'decision)
          equality-decidable
          (function/lam
           [['left 'S] ['right 'S]]
           (app
            (function/const*
             'finite/equality-decidable-of-certified-decision [U])
            'S 'decision 'certified 'left 'right))
          off-diagonal
          (app
           (function/const*
            'mcmc/nnrat-hastings-diagonal-rejection-placement-off-diagonal-zero
            [U])
           'S 'states 'target 'proposal 'decision 'certified)
          placement-total
          (app
           (function/const*
            'mcmc/nnrat-hastings-diagonal-rejection-placement-has-rejection-mass
            [U])
           'S 'states 'target 'proposal 'decision
           'certified 'carrier-covered)]
      (app
       (function/const*
        'mcmc/nnrat-hastings-completed-kernel-stationary-of-off-diagonal-zero
        [U])
       'S 'states 'target 'proposal placement
       equality-decidable off-diagonal
       'target-normalized 'proposal-normalized placement-total)))})

(def hastings-canonical-kernel-stationary-of-exhaustive-carrier-spec
  {:name 'mcmc/nnrat-hastings-canonical-kernel-stationary-of-exhaustive-carrier
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]]
    (stationary
     'S 'states
     (canonical-kernel 'S 'states 'target 'proposal 'decision)
     'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['exhaustive (exhaustive-carrier 'S 'states 'decision)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['proposal-normalized (kernel-normalized 'S 'states 'proposal)]]
    (let [certified
          (app
           (function/const*
            'finite/certified-equality-of-exhaustive-carrier [U])
           'S 'states 'decision 'exhaustive)
          covered
          (app
           (function/const* 'finite/coverage-of-exhaustive-carrier [U])
           'S 'states 'decision 'exhaustive)]
      (app
       (function/const*
        'mcmc/nnrat-hastings-canonical-kernel-stationary [U])
       'S 'states 'target 'proposal 'decision
       certified covered 'target-normalized 'proposal-normalized)))})

(def hastings-realization-detailed-balance-spec
  {:name 'mcmc/nnrat-hastings-realization-detailed-balance
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]
     ['realized (realization 'S 'target 'proposal 'kernel 'correction)]
     ['correction-symmetric (symmetric-flow 'S 'correction)]]
    (detailed-balance 'S 'target 'kernel))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]
     ['realized (realization 'S 'target 'proposal 'kernel 'correction)]
     ['correction-symmetric (symmetric-flow 'S 'correction)]]
    (function/lam
     [['left 'S] ['right 'S]]
     (let [left-product
           (rmul (app 'target 'left) (app 'kernel 'left 'right))
           right-product
           (rmul (app 'target 'right) (app 'kernel 'right 'left))
           left-flow
           (accepted-flow 'S 'target 'proposal 'left 'right)
           right-flow
           (accepted-flow 'S 'target 'proposal 'right 'left)
           left-correction (app 'correction 'left 'right)
           right-correction (app 'correction 'right 'left)
           left-sum (radd left-flow left-correction)
           right-sum (radd right-flow right-correction)
           middle-same
           (add-respects
            left-flow right-flow left-correction right-correction
            (app
             (function/const*
              'mcmc/nnrat-hastings-accepted-flow-symmetric [U])
             'S 'target 'proposal 'left 'right)
            (app 'correction-symmetric 'left 'right))]
       (equivalent-transitive
        left-product left-sum right-product
        (app 'realized 'left 'right)
        (equivalent-transitive
         left-sum right-sum right-product
         middle-same
         (equivalent-symmetric
          right-product right-sum
          (app 'realized 'right 'left)))))))})

(def hastings-realization-stationary-spec
  {:name 'mcmc/nnrat-hastings-realization-stationary
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['realized (realization 'S 'target 'proposal 'kernel 'correction)]
     ['correction-symmetric (symmetric-flow 'S 'correction)]]
    (stationary 'S 'states 'kernel 'target))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['correction (function/arrow 'S 'S nnrat)]
     ['target-normalized
      (req (total-mass 'S 'states 'target) nnrat-one)]
     ['kernel-normalized (kernel-normalized 'S 'states 'kernel)]
     ['realized (realization 'S 'target 'proposal 'kernel 'correction)]
     ['correction-symmetric (symmetric-flow 'S 'correction)]]
    (app
     (function/const*
      'markov/nnrat-detailed-balance-implies-stationary [U])
     'S 'states 'kernel 'target 'kernel-normalized
     (app
      (function/const*
       'mcmc/nnrat-hastings-realization-detailed-balance [U])
      'S 'target 'proposal 'kernel 'correction
      'realized 'correction-symmetric)))})

(def definition-specs
  [hastings-accepted-flow-spec
   hastings-ratio-acceptance-spec
   hastings-accepted-transition-spec
   hastings-rejection-mass-spec
   hastings-completed-kernel-spec
   hastings-rejection-correction-spec
   off-diagonal-zero-spec
   hastings-diagonal-rejection-placement-spec
   hastings-canonical-kernel-spec
   symmetric-flow-spec
   hastings-kernel-realization-spec])

(def theorem-specs
  [min-commutative-spec
   hastings-accepted-flow-symmetric-spec
   positive-hastings-ratio-realizes-accepted-flow-spec
   zero-hastings-ratio-realizes-accepted-flow-spec
   made-hastings-ratio-realizes-accepted-flow-spec
   hastings-ratio-realizes-accepted-flow-spec
   positive-hastings-ratio-acceptance-at-most-one-spec
   zero-hastings-ratio-acceptance-at-most-one-spec
   made-hastings-ratio-acceptance-at-most-one-spec
   hastings-ratio-acceptance-at-most-one-spec
   hastings-accepted-transition-at-most-proposal-spec
   hastings-accepted-transition-realizes-flow-spec
   hastings-accepted-row-at-most-proposal-row-spec
   hastings-accepted-row-at-most-one-spec
   hastings-accepted-row-plus-rejection-is-one-spec
   hastings-completed-kernel-rows-normalized-spec
   hastings-completed-kernel-realization-spec
   hastings-rejection-correction-symmetric-of-off-diagonal-zero-spec
   hastings-realization-detailed-balance-spec
   hastings-realization-stationary-spec
   hastings-completed-kernel-detailed-balance-spec
   hastings-completed-kernel-stationary-spec
   hastings-completed-kernel-stationary-of-off-diagonal-zero-spec
   hastings-diagonal-rejection-placement-off-diagonal-zero-spec
   hastings-diagonal-rejection-placement-has-rejection-mass-spec
   hastings-canonical-kernel-stationary-spec
   hastings-canonical-kernel-stationary-of-exhaustive-carrier-spec])

(defn- extend-spec-if-missing [env alias milestone spec]
  (if (environment/resolve-id env alias)
    env
    (support/extend-with env milestone [spec])))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.metric-separation rainbow.math.finite.markov-stationarity])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (extend-spec-if-missing 'nnrat/multiply-one-right :finite-markov-hastings-flow-support identities/multiply-one-right-spec) (extend-spec-if-missing 'nnrat/multiply-zero-left :finite-markov-hastings-flow-support identities/multiply-zero-left-spec) (extend-spec-if-missing 'nnrat/multiply-zero-right :finite-markov-hastings-flow-support identities/multiply-zero-right-spec) (extend-spec-if-missing 'nnrat/add-zero-left :finite-markov-hastings-flow-support identities/add-zero-left-spec) (extend-spec-if-missing 'nnrat/multiply-monotone-base :finite-markov-hastings-flow-support multiply-monotone/multiply-monotone-base-spec) (extend-spec-if-missing 'nnrat/multiply-monotone :finite-markov-hastings-flow-support multiply-monotone/multiply-monotone-spec) (extend-spec-if-missing 'nnrat/map-sum-monotone :finite-markov-hastings-flow-support list-sum/map-sum-monotone-spec) (extend-spec-if-missing 'nnrat/multiply-associative :finite-markov-hastings-flow-support reassociation/multiply-associative-spec) (extend-spec-if-missing 'nnrat/multiply-swap-right :finite-markov-hastings-flow-support reassociation/multiply-swap-right-spec) (extend-spec-if-missing 'nnrat/at-most-multiply-left-cancel :finite-markov-hastings-flow-support order-scale/at-most-multiply-left-cancel-spec) (extend-spec-if-missing 'nnrat/multiply-divide-cancel :finite-markov-hastings-flow-support order-scale/multiply-divide-cancel-spec) (extend-spec-if-missing 'nnrat/at-most-multiply-left-normalize-lower :finite-markov-hastings-flow-support order-scale/normalize-lower-spec) (extend-spec-if-missing 'nat/add-distance-of-at-most :finite-markov-hastings-flow-support ordered-distance/nat-add-distance-of-at-most-spec) (extend-spec-if-missing 'nnrat/add-distance-of-at-most :finite-markov-hastings-flow-support ordered-distance/nnrat-add-distance-of-at-most-spec) (extend-spec-if-missing 'nnrat/add-associative :finite-markov-hastings-flow-support add-reassociation/add-associative-spec) (extend-spec-if-missing 'nnrat/add-swap-right :finite-markov-hastings-flow-support add-reassociation/add-swap-right-spec) (extend-spec-if-missing 'nnrat/add-four-reorder :finite-markov-hastings-flow-support add-reassociation/add-four-reorder-spec) (extend-spec-if-missing 'nnrat/map-sum-add :finite-markov-hastings-flow-support sum-additive/map-sum-add-spec) (extend-spec-if-missing 'finite/certified-equality-decision :finite-markov-hastings-flow-support diagonal-spike/certified-equality-decision-spec) (extend-spec-if-missing 'finite/certified-exhaustive-carrier :finite-markov-hastings-flow-support diagonal-spike/certified-exhaustive-carrier-spec) (extend-spec-if-missing 'finite/certified-equality-of-exhaustive-carrier :finite-markov-hastings-flow-support diagonal-spike/certified-equality-of-exhaustive-carrier-spec) (extend-spec-if-missing 'finite/coverage-of-exhaustive-carrier :finite-markov-hastings-flow-support diagonal-spike/coverage-of-exhaustive-carrier-spec) (extend-spec-if-missing 'finite/nnrat-diagonal-spike :finite-markov-hastings-flow-support diagonal-spike/diagonal-spike-spec) (extend-spec-if-missing 'finite/nnrat-diagonal-spike-zero-of-different :finite-markov-hastings-flow-support diagonal-spike/diagonal-spike-zero-of-different-spec) (extend-spec-if-missing 'finite/equality-decidable-of-certified-decision :finite-markov-hastings-flow-support diagonal-spike/equality-decidable-of-certified-decision-spec) (extend-spec-if-missing 'finite/nnrat-diagonal-spike-mass-of-equal :finite-markov-hastings-flow-support diagonal-spike/diagonal-spike-mass-of-equal-spec) (extend-spec-if-missing 'finite/nnrat-map-sum-diagonal-spike-zero-of-not-member :finite-markov-hastings-flow-support diagonal-spike/map-sum-diagonal-spike-zero-of-not-member-spec) (extend-spec-if-missing 'finite/nnrat-map-sum-diagonal-spike-of-member-no-duplicates :finite-markov-hastings-flow-support diagonal-spike/map-sum-diagonal-spike-of-member-no-duplicates-spec) (extend-spec-if-missing 'finite/nnrat-finset-diagonal-spike-total :finite-markov-hastings-flow-support diagonal-spike/finset-diagonal-spike-total-spec) (support/extend-with :finite-markov-hastings-flow (concat definition-specs theorem-specs))))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-hastings-flow))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
