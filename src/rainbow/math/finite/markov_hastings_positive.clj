(ns rainbow.math.finite.markov-hastings-positive
  "Strict-positivity certificates for division-free Hastings transitions.

  If both directed target-proposal products are positive, then their minimum
  (the accepted flow) is positive.  The same hypotheses make the ratio
  acceptance positive; multiplying by the positive forward proposal therefore
  makes the accepted transition positive.  These are the mathematical bridge
  from full-support target/proposal data to one-step reachability.

  Native, kernel-checked, and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.markov-hastings-flow :as flow]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.positive :as nnrat-positive]))

(def zero-level [:zero])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def bool (function/const* 'data/Bool []))

(defn- app [f & xs] (apply function/app f xs))
(defn- multiply [left right]
  (app (function/const* 'nnrat/multiply []) left right))
(defn- minimum [left right]
  (app (function/const* 'minmax/min []) left right))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- ratio-acceptance [forward reverse]
  (app (function/const* 'mcmc/nnrat-hastings-ratio-acceptance [])
       forward reverse))
(defn- accepted-flow [element target proposal left right]
  (app (function/const* 'mcmc/nnrat-hastings-accepted-flow [U])
       element target proposal left right))
(defn- accepted-transition [element target proposal left right]
  (app (function/const* 'mcmc/nnrat-hastings-accepted-transition [U])
       element target proposal left right))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- completed-kernel [element states target proposal placement left right]
  (app (function/const* 'mcmc/nnrat-hastings-completed-kernel [U])
       element states target proposal placement left right))
(defn- diagonal-rejection-placement
  [element states target proposal decision]
  (app
   (function/const*
    'mcmc/nnrat-hastings-diagonal-rejection-placement [U])
   element states target proposal decision))
(defn- canonical-kernel [element states target proposal decision left right]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [U])
       element states target proposal decision left right))

(def hastings-ratio-acceptance-positive-spec
  {:name 'mcmc/nnrat-hastings-ratio-acceptance-positive
   :universes []
   :type
   (function/forall
    [['forward nnrat] ['reverse nnrat]
     ['forward-positive (positive 'forward)]
     ['reverse-positive (positive 'reverse)]]
    (positive (ratio-acceptance 'forward 'reverse)))
   :value
   (function/lam
    [['forward nnrat] ['reverse nnrat]
     ['forward-positive (positive 'forward)]
     ['reverse-positive (positive 'reverse)]]
    (app
     (function/const* 'nnrat/divide-positive-left [])
     (minimum 'forward 'reverse) 'forward
     (app
      (function/const* 'nnrat/min-positive [])
      'forward 'reverse 'forward-positive 'reverse-positive)))})

(def hastings-accepted-flow-positive-spec
  {:name 'mcmc/nnrat-hastings-accepted-flow-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (positive (accepted-flow 'S 'target 'proposal 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (let [forward
          (multiply (app 'target 'left) (app 'proposal 'left 'right))
          reverse
          (multiply (app 'target 'right) (app 'proposal 'right 'left))
          forward-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'target 'left) (app 'proposal 'left 'right)
           'target-left-positive 'proposal-forward-positive)
          reverse-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'target 'right) (app 'proposal 'right 'left)
           'target-right-positive 'proposal-reverse-positive)]
      (app
       (function/const* 'nnrat/min-positive [])
       forward reverse forward-positive reverse-positive)))})

(def hastings-accepted-transition-positive-spec
  {:name 'mcmc/nnrat-hastings-accepted-transition-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (positive (accepted-transition 'S 'target 'proposal 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (let [forward
          (multiply (app 'target 'left) (app 'proposal 'left 'right))
          reverse
          (multiply (app 'target 'right) (app 'proposal 'right 'left))
          forward-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'target 'left) (app 'proposal 'left 'right)
           'target-left-positive 'proposal-forward-positive)
          reverse-positive
          (app
           (function/const* 'nnrat/multiply-positive [])
           (app 'target 'right) (app 'proposal 'right 'left)
           'target-right-positive 'proposal-reverse-positive)
          acceptance-positive
          (app
           (function/const*
            'mcmc/nnrat-hastings-ratio-acceptance-positive [])
           forward reverse forward-positive reverse-positive)]
      (app
       (function/const* 'nnrat/multiply-positive [])
       (app 'proposal 'left 'right)
       (ratio-acceptance forward reverse)
       'proposal-forward-positive acceptance-positive)))})

(def hastings-completed-kernel-positive-spec
  {:name 'mcmc/nnrat-hastings-completed-kernel-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (positive
     (completed-kernel
      'S 'states 'target 'proposal 'placement 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['placement (function/arrow 'S 'S nnrat)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (let [accepted
          (accepted-transition 'S 'target 'proposal 'left 'right)]
      (app
       (function/const* 'nnrat/add-positive-left [])
       accepted (app 'placement 'left 'right)
       (app
        (function/const*
         'mcmc/nnrat-hastings-accepted-transition-positive [U])
        'S 'target 'proposal 'left 'right
        'target-left-positive 'proposal-forward-positive
        'target-right-positive 'proposal-reverse-positive))))})

(def hastings-canonical-kernel-positive-spec
  {:name 'mcmc/nnrat-hastings-canonical-kernel-positive
   :universes ['u]
   :type
   (function/forall
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (positive
     (canonical-kernel
      'S 'states 'target 'proposal 'decision 'left 'right)))
   :value
   (function/lam
    [['S type-u]
     ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]
     ['decision (function/arrow 'S 'S bool)]
     ['left 'S] ['right 'S]
     ['target-left-positive (positive (app 'target 'left))]
     ['proposal-forward-positive (positive (app 'proposal 'left 'right))]
     ['target-right-positive (positive (app 'target 'right))]
     ['proposal-reverse-positive (positive (app 'proposal 'right 'left))]]
    (app
     (function/const* 'mcmc/nnrat-hastings-completed-kernel-positive [U])
     'S 'states 'target 'proposal
     (diagonal-rejection-placement
      'S 'states 'target 'proposal 'decision)
     'left 'right
     'target-left-positive 'proposal-forward-positive
     'target-right-positive 'proposal-reverse-positive))})

(def definition-specs [])
(def theorem-specs
  [hastings-ratio-acceptance-positive-spec
   hastings-accepted-flow-positive-spec
   hastings-accepted-transition-positive-spec
   hastings-completed-kernel-positive-spec
   hastings-canonical-kernel-positive-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-hastings-flow rainbow.math.rational.nnrat.positive])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :finite-markov-hastings-positive theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.finite.markov-hastings-positive))
(defn definition-ids [env] (support/spec-ids env definition-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
