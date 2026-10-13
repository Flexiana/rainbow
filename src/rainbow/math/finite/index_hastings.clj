(ns rainbow.math.finite.index-hastings
  "The canonical Hastings kernel instantiated on structural finite indices.

  This closes the obligation left open earlier, one step
  further than stated: they asked for index-equality soundness and then this
  assembly, and pushed the soundness themselves in a final commit, so what
  remained -- and what this module is -- is the assembly.  Three declarations:

  - the certified equality decision for `Index n`, the conjunction of the
    soundness and completeness theorems the finite-index module already
    carries, at every bound;
  - the certified exhaustive carrier for `Index n` with its canonical finset:
    the decision certificate conjoined with enumeration coverage.  The
    carrier-covered premise that was found by needing it holds here BY
    CONSTRUCTION -- `Index n` has no inhabitants outside its enumeration;
  - the capstone: for EVERY bound n, every normalized exact-rational target
    and proposal over `Index n`, the canonical Hastings kernel -- ratio
    acceptance, diagonal rejection, nothing supplied but the two
    normalization facts -- is stationary for the target.

  This is the first fully-instantiated MCMC stationarity statement in the
  corpus: no abstract carrier, no supplied placement, no equality hypothesis,
  no coverage hypothesis.  Everything the caller once certified is now proved
  from the structure of `Index`.  Still Level 3 and stated so: nothing here
  samples, and no executable claim is made.  Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.finite.index :as index]
            [rainbow.math.finite.markov-hastings-flow :as hastings]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-one (function/const* 'nnrat/one []))

(defn- app [f & args] (apply function/app f args))
(defn- index-of [upper] (app (function/const* 'finite/Index []) upper))
(defn- decide [upper]
  (app (function/const* 'finite/index-decide-equality []) upper))
(defn- index-finset [upper]
  (app (function/const* 'finite/index-finset []) upper))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- certified-equality [element decision]
  (app (function/const* 'finite/certified-equality-decision [zero-level])
       element decision))
(defn- exhaustive-carrier [element states decision]
  (app (function/const* 'finite/certified-exhaustive-carrier [zero-level])
       element states decision))
(defn- conjoin [left right left-evidence right-evidence]
  (app (function/const* 'proposition/conjoin [])
       left right left-evidence right-evidence))
(defn- equality-soundness-prop [element decision]
  (function/forall
   [['left element] ['right element]
    ['accepted (function/equality type-level bool
                                  (app decision 'left 'right)
                                  (function/const* 'data/true []))]]
   (function/equality type-level element 'left 'right)))
(defn- equality-completeness-prop [element decision]
  (function/forall
   [['left element] ['right element]
    ['same (function/equality type-level element 'left 'right)]]
   (function/equality type-level bool (app decision 'left 'right)
                      (function/const* 'data/true []))))
(defn- carrier-covered-prop [element states]
  (function/forall
   [['state element]]
   (app (function/const* 'list/membership [zero-level])
        element
        (app (function/const* 'finset-data/enumeration [zero-level])
             element states)
        'state)))

(def certified-equality-decision-spec
  {:name 'finite/index-certified-equality-decision :universes []
   :type
   (function/forall
    [['upper nat]]
    (certified-equality (index-of 'upper) (decide 'upper)))
   :value
   (function/lam
    [['upper nat]]
    (conjoin
     (equality-soundness-prop (index-of 'upper) (decide 'upper))
     (equality-completeness-prop (index-of 'upper) (decide 'upper))
     (app (function/const* 'finite/index-decide-equality-true-sound []) 'upper)
     (app (function/const* 'finite/index-equality-implies-decide-equality-true [])
          'upper)))})

(def certified-exhaustive-carrier-spec
  {:name 'finite/index-certified-exhaustive-carrier :universes []
   :type
   (function/forall
    [['upper nat]]
    (exhaustive-carrier (index-of 'upper) (index-finset 'upper)
                        (decide 'upper)))
   :value
   (function/lam
    [['upper nat]]
    (conjoin
     (certified-equality (index-of 'upper) (decide 'upper))
     (carrier-covered-prop (index-of 'upper) (index-finset 'upper))
     (app (function/const* 'finite/index-certified-equality-decision []) 'upper)
     (app (function/const* 'finite/index-enumeration-covers []) 'upper)))})

(defn- total-mass [element states weights]
  (app (function/const* 'probability/nnrat-total-mass [zero-level])
       element states weights))
(defn- kernel-normalized [element states kernel]
  (app (function/const* 'markov/nnrat-kernel-rows-normalized [zero-level])
       element states kernel))
(defn- canonical-kernel [element states target proposal decision]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [zero-level])
       element states target proposal decision))
(defn- stationary [element states kernel target]
  (app (function/const* 'markov/nnrat-stationary [zero-level])
       element states kernel target))

(def index-canonical-kernel-stationary-spec
  {:name 'mcmc/nnrat-hastings-index-canonical-kernel-stationary :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['target-normalized
      (req (total-mass (index-of 'upper) (index-finset 'upper) 'target)
           nnrat-one)]
     ['proposal-normalized
      (kernel-normalized (index-of 'upper) (index-finset 'upper) 'proposal)]]
    (stationary (index-of 'upper) (index-finset 'upper)
                (canonical-kernel (index-of 'upper) (index-finset 'upper)
                                  'target 'proposal (decide 'upper))
                'target))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['target-normalized
      (req (total-mass (index-of 'upper) (index-finset 'upper) 'target)
           nnrat-one)]
     ['proposal-normalized
      (kernel-normalized (index-of 'upper) (index-finset 'upper) 'proposal)]]
    (app
     (function/const*
      'mcmc/nnrat-hastings-canonical-kernel-stationary-of-exhaustive-carrier
      [zero-level])
     (index-of 'upper) (index-finset 'upper) 'target 'proposal (decide 'upper)
     (app (function/const* 'finite/index-certified-exhaustive-carrier [])
          'upper)
     'target-normalized 'proposal-normalized))})

(def theorem-specs
  [certified-equality-decision-spec
   certified-exhaustive-carrier-spec
   index-canonical-kernel-stationary-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-hastings-flow rainbow.math.finite.index])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-index-hastings theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.index-hastings))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
