(ns rainbow.math.finite.markov-full-support
  "An executable full-support decision, and what its verdict is worth.

  The positivity cone gives pointwise theorems: positive target here, positive
  proposal there, positive canonical-kernel entry. A CALLER holds a whole
  model, and the honest interface is a single boolean they can compute:
  full-support-decision folds an executable positivity check over the finite
  enumeration -- every target mass, every proposal edge in both directions --
  and this module's theorems make a true verdict discharge EVERY pointwise
  positivity hypothesis at once, for every state the carrier covers.

  On structural Index n, where coverage is by construction, the two capstones
  follow with no hypothesis beyond the verdict: every canonical-kernel entry
  is positive, and from every state, one step of the actual mass iterator
  started at the certified point mass puts positive mass on every state.
  That second statement is one-step reachability -- the exists-n
  irreducibility definition's n = 1 witness, stated without yet defining
  irreducibility, per the agreed split: the path-induction engine below this
  API is an earlier cone; this module adds the decision layer and its wiring.

  The decision is deliberately naive -- a fold of numerator-positivity over
  enumerations, quadratic in states -- because its job is to be READ and to be
  sound, not to be fast. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.boolean-and :as boolean-and]
            [rainbow.math.finite.index-hastings :as index-hastings]
            [rainbow.math.finite.markov-point-mass :as point-mass]
            [rainbow.math.finite.markov-hastings-positive :as positive]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def bool (function/const* 'data/Bool []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def true-value (function/const* 'data/true []))
(def false-value (function/const* 'data/false []))
(def nat-zero (function/const* 'data/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- list-of [element]
  (app (function/const* 'data/List [data-u]) element))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- eq-bool [left right]
  (function/equality type-level bool left right))
(defn- both [left right] (app (function/const* 'boolean/and []) left right))
(defn- positive [value]
  (app (function/const* 'nnrat/positive []) value))
(defn- numerator-of [value]
  (app (function/const* 'nnrat/numerator []) value))
(defn- explode [goal proof]
  (app (function/const* 'proposition/explode []) goal proof))
(defn- false-not-true [proof]
  (app (function/const* 'bool/false-not-true []) proof))
(defn- and-left [a b proof]
  (app (function/const* 'boolean/and-implies-left []) a b proof))
(defn- and-right [a b proof]
  (app (function/const* 'boolean/and-implies-right []) a b proof))
(defn- use-disjunction [left right goal evidence on-left on-right]
  (app (function/const* 'proposition/use-disjunction [])
       left right goal evidence on-left on-right))
(defn- reverse-substitution [level carrier x y proof predicate at-y]
  (app (function/const* 'equality/reverse-substitution [level])
       carrier x y proof predicate at-y))

;; ---- the executable positivity check ----------------------------------------

(def decide-positive-spec
  {:name 'mcmc/decide-positive :kind :definition :universes []
   :transparency :reducible
   :type (function/arrow nnrat bool)
   :value
   (function/lam
    [['value nnrat]]
    (app (function/const* 'data/Nat.rec [type-level])
         (function/lam [['ignored nat]] bool)
         false-value
         (function/lam [['predecessor nat] ['recursive bool]] true-value)
         (numerator-of 'value)))})

(defn- decide-positive [value]
  (app (function/const* 'mcmc/decide-positive []) value))

(def decide-positive-true-sound-spec
  "A true verdict IS positivity. The numerator is case-split by Nat.rec at a
  motive over the raw natural: zero refutes the verdict, and a successor
  supplies the strict-below witness directly -- the arithmetic is definitional
  because nat addition recurses on its left argument."
  {:name 'mcmc/decide-positive-true-sound :universes []
   :type
   (function/forall
    [['value nnrat]]
    (function/arrow (eq-bool (decide-positive 'value) true-value)
                    (positive 'value)))
   :value
   (function/lam
    [['value nnrat]]
    (app
     (function/const* 'data/Nat.rec [zero-level])
     (function/lam
      [['raw nat]]
      (function/arrow
       (eq-bool (app (function/const* 'data/Nat.rec [type-level])
                     (function/lam [['ignored nat]] bool)
                     false-value
                     (function/lam [['predecessor nat] ['recursive bool]]
                                   true-value)
                     'raw)
                true-value)
       (app (function/const* 'nat/strict-below []) nat-zero 'raw)))
     (function/lam
      [['verdict (eq-bool false-value true-value)]]
      (explode (app (function/const* 'nat/strict-below []) nat-zero nat-zero)
               (false-not-true 'verdict)))
     (function/lam
      [['predecessor nat]
       ['ignored-recursive
        (function/arrow
         (eq-bool (app (function/const* 'data/Nat.rec [type-level])
                       (function/lam [['ignored nat]] bool)
                       false-value
                       (function/lam [['p nat] ['r bool]] true-value)
                       'predecessor)
                  true-value)
         (app (function/const* 'nat/strict-below []) nat-zero 'predecessor))]
       ['verdict (eq-bool true-value true-value)]]
      (app (function/const* 'proposition/witness [type-level])
           nat
           (function/lam
            [['extra nat]]
            (function/equality
             type-level nat
             (app (function/const* 'algebra/nat-add [])
                  (succ nat-zero) 'extra)
             (succ 'predecessor)))
           'predecessor
           (app (function/const* 'equality/reflexive [type-level])
                nat (succ 'predecessor))))
     (numerator-of 'value)))})

;; ---- folds over enumerations ------------------------------------------------

(def all-positive-spec
  {:name 'mcmc/all-positive :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['weights (function/arrow 'S nnrat)]
     ['items (list-of 'S)]]
    bool)
   :value
   (function/lam
    [['S type-u] ['weights (function/arrow 'S nnrat)]
     ['items (list-of 'S)]]
    (app (function/const* 'data/List.rec [data-u type-level])
         'S
         (function/lam [['ignored (list-of 'S)]] bool)
         true-value
         (function/lam
          [['head 'S] ['tail (list-of 'S)] ['rest bool]]
          (both (decide-positive (app 'weights 'head)) 'rest))
         'items))})

(defn- all-positive [element weights items]
  (app (function/const* 'mcmc/all-positive [U]) element weights items))

(def all-pairs-positive-spec
  {:name 'mcmc/all-pairs-positive :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['kernel (function/arrow 'S 'S nnrat)]
     ['sources (list-of 'S)] ['targets (list-of 'S)]]
    bool)
   :value
   (function/lam
    [['S type-u] ['kernel (function/arrow 'S 'S nnrat)]
     ['sources (list-of 'S)] ['targets (list-of 'S)]]
    (app (function/const* 'data/List.rec [data-u type-level])
         'S
         (function/lam [['ignored (list-of 'S)]] bool)
         true-value
         (function/lam
          [['head 'S] ['tail (list-of 'S)] ['rest bool]]
          (both (all-positive 'S (app 'kernel 'head) 'targets) 'rest))
         'sources))})

(defn- all-pairs-positive [element kernel sources targets]
  (app (function/const* 'mcmc/all-pairs-positive [U])
       element kernel sources targets))

(def full-support-decision-spec
  {:name 'mcmc/full-support-decision :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]]
    bool)
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['target (function/arrow 'S nnrat)]
     ['proposal (function/arrow 'S 'S nnrat)]]
    (both (all-positive 'S 'target (enumeration 'S 'states))
          (all-pairs-positive 'S 'proposal
                              (enumeration 'S 'states)
                              (enumeration 'S 'states))))})

(defn- full-support-decision [element states target proposal]
  (app (function/const* 'mcmc/full-support-decision [U])
       element states target proposal))

;; ---- soundness of the folds -------------------------------------------------

(def all-positive-member-sound-spec
  "A true fold makes every LISTED weight positive: list induction, splitting
  the AND at each cons and transporting the head case along the membership
  equality."
  {:name 'mcmc/all-positive-member-sound :universes ['u]
   :type
   (function/forall
    [['S type-u] ['weights (function/arrow 'S nnrat)]
     ['items (list-of 'S)]]
    (function/arrow
     (eq-bool (all-positive 'S 'weights 'items) true-value)
     (function/forall
      [['value 'S] ['member (membership 'S 'items 'value)]]
      (positive (app 'weights 'value)))))
   :value
   (function/lam
    [['S type-u] ['weights (function/arrow 'S nnrat)]
     ['items (list-of 'S)]]
    (app
     (function/const* 'data/List.rec [data-u zero-level])
     'S
     (function/lam
      [['current (list-of 'S)]]
      (function/arrow
       (eq-bool (all-positive 'S 'weights 'current) true-value)
       (function/forall
        [['value 'S] ['member (membership 'S 'current 'value)]]
        (positive (app 'weights 'value)))))
     (function/lam
      [['verdict (eq-bool true-value true-value)]
       ['value 'S] ['member (proposition/falsity)]]
      (explode (positive (app 'weights 'value)) 'member))
     (function/lam
      [['head 'S] ['tail (list-of 'S)]
       ['tail-sound
        (function/arrow
         (eq-bool (all-positive 'S 'weights 'tail) true-value)
         (function/forall
          [['value 'S] ['member (membership 'S 'tail 'value)]]
          (positive (app 'weights 'value))))]
       ['verdict
        (eq-bool (both (decide-positive (app 'weights 'head))
                       (all-positive 'S 'weights 'tail))
                 true-value)]
       ['value 'S]
       ['member
        (proposition/disjunction
         (function/equality data-u 'S 'value 'head)
         (membership 'S 'tail 'value))]]
      (use-disjunction
       (function/equality data-u 'S 'value 'head)
       (membership 'S 'tail 'value)
       (positive (app 'weights 'value))
       'member
       (function/lam
        [['same (function/equality data-u 'S 'value 'head)]]
        (reverse-substitution
         data-u 'S 'value 'head 'same
         (function/lam [['other 'S]] (positive (app 'weights 'other)))
         (app (function/const* 'mcmc/decide-positive-true-sound [])
              (app 'weights 'head)
              (and-left (decide-positive (app 'weights 'head))
                        (all-positive 'S 'weights 'tail)
                        'verdict))))
       (function/lam
        [['rest (membership 'S 'tail 'value)]]
        (app 'tail-sound
             (and-right (decide-positive (app 'weights 'head))
                        (all-positive 'S 'weights 'tail)
                        'verdict)
             'value 'rest))))
     'items))})

(def all-pairs-member-sound-spec
  "The two-dimensional version: induction over sources, with the row handled by
  the one-dimensional soundness and the head transported the same way."
  {:name 'mcmc/all-pairs-positive-member-sound :universes ['u]
   :type
   (function/forall
    [['S type-u] ['kernel (function/arrow 'S 'S nnrat)]
     ['sources (list-of 'S)] ['targets (list-of 'S)]]
    (function/arrow
     (eq-bool (all-pairs-positive 'S 'kernel 'sources 'targets) true-value)
     (function/forall
      [['source 'S] ['destination 'S]
       ['source-member (membership 'S 'sources 'source)]
       ['destination-member (membership 'S 'targets 'destination)]]
      (positive (app 'kernel 'source 'destination)))))
   :value
   (function/lam
    [['S type-u] ['kernel (function/arrow 'S 'S nnrat)]
     ['sources (list-of 'S)] ['targets (list-of 'S)]]
    (app
     (function/const* 'data/List.rec [data-u zero-level])
     'S
     (function/lam
      [['current (list-of 'S)]]
      (function/arrow
       (eq-bool (all-pairs-positive 'S 'kernel 'current 'targets) true-value)
       (function/forall
        [['source 'S] ['destination 'S]
         ['source-member (membership 'S 'current 'source)]
         ['destination-member (membership 'S 'targets 'destination)]]
        (positive (app 'kernel 'source 'destination)))))
     (function/lam
      [['verdict (eq-bool true-value true-value)]
       ['source 'S] ['destination 'S]
       ['source-member (proposition/falsity)]
       ['destination-member (membership 'S 'targets 'destination)]]
      (explode (positive (app 'kernel 'source 'destination)) 'source-member))
     (function/lam
      [['head 'S] ['tail (list-of 'S)]
       ['tail-sound
        (function/arrow
         (eq-bool (all-pairs-positive 'S 'kernel 'tail 'targets) true-value)
         (function/forall
          [['source 'S] ['destination 'S]
           ['source-member (membership 'S 'tail 'source)]
           ['destination-member (membership 'S 'targets 'destination)]]
          (positive (app 'kernel 'source 'destination))))]
       ['verdict
        (eq-bool (both (all-positive 'S (app 'kernel 'head) 'targets)
                       (all-pairs-positive 'S 'kernel 'tail 'targets))
                 true-value)]
       ['source 'S] ['destination 'S]
       ['source-member
        (proposition/disjunction
         (function/equality data-u 'S 'source 'head)
         (membership 'S 'tail 'source))]
       ['destination-member (membership 'S 'targets 'destination)]]
      (use-disjunction
       (function/equality data-u 'S 'source 'head)
       (membership 'S 'tail 'source)
       (positive (app 'kernel 'source 'destination))
       'source-member
       (function/lam
        [['same (function/equality data-u 'S 'source 'head)]]
        (reverse-substitution
         data-u 'S 'source 'head 'same
         (function/lam [['other 'S]]
                       (positive (app 'kernel 'other 'destination)))
         (app (function/const* 'mcmc/all-positive-member-sound [U])
              'S (app 'kernel 'head) 'targets
              (and-left (all-positive 'S (app 'kernel 'head) 'targets)
                        (all-pairs-positive 'S 'kernel 'tail 'targets)
                        'verdict)
              'destination 'destination-member)))
       (function/lam
        [['rest (membership 'S 'tail 'source)]]
        (app 'tail-sound
             (and-right (all-positive 'S (app 'kernel 'head) 'targets)
                        (all-pairs-positive 'S 'kernel 'tail 'targets)
                        'verdict)
             'source 'destination 'rest 'destination-member))))
     'sources))})

;; ---- the Index capstones ----------------------------------------------------
;; Everything below is at universes [], so the polymorphic helpers above are
;; re-instantiated at zero here; using the [U] versions inside a []-universe
;; declaration is an unbound-universe rejection, which the kernel duly issued.

(defn- enumeration0 [element source]
  (app (function/const* 'finset-data/enumeration [zero-level]) element source))
(defn- all-positive0 [element weights items]
  (app (function/const* 'mcmc/all-positive [zero-level]) element weights items))
(defn- all-pairs-positive0 [element kernel sources targets]
  (app (function/const* 'mcmc/all-pairs-positive [zero-level])
       element kernel sources targets))
(defn- full-support-decision0 [element states target proposal]
  (app (function/const* 'mcmc/full-support-decision [zero-level])
       element states target proposal))

(defn- index-of [upper] (app (function/const* 'finite/Index []) upper))
(defn- index-finset [upper]
  (app (function/const* 'finite/index-finset []) upper))
(defn- index-decide [upper]
  (app (function/const* 'finite/index-decide-equality []) upper))
(defn- covers [upper state]
  (app (function/const* 'finite/index-enumeration-covers []) upper state))
(defn- canonical-kernel [element states target proposal decision]
  (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel [zero-level])
       element states target proposal decision))

(def index-kernel-positive-spec
  "One computed boolean discharges every pointwise positivity hypothesis: on
  Index n coverage is by construction, so a true full-support verdict makes
  EVERY canonical-kernel entry positive."
  {:name 'mcmc/nnrat-hastings-index-canonical-kernel-positive-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (eq-bool (full-support-decision0 (index-of 'upper) (index-finset 'upper)
                                      'target 'proposal)
               true-value)]
     ['left (index-of 'upper)] ['right (index-of 'upper)]]
    (positive
     (app (canonical-kernel (index-of 'upper) (index-finset 'upper)
                            'target 'proposal (index-decide 'upper))
          'left 'right)))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (eq-bool (full-support-decision0 (index-of 'upper) (index-finset 'upper)
                                      'target 'proposal)
               true-value)]
     ['left (index-of 'upper)] ['right (index-of 'upper)]]
    (let [element (index-of 'upper)
          states (index-finset 'upper)
          enum (enumeration0 element states)
          target-part (all-positive0 element 'target enum)
          proposal-part (all-pairs-positive0 element 'proposal enum enum)
          target-positive
          (fn [state]
            (app (function/const* 'mcmc/all-positive-member-sound [zero-level])
                 element 'target enum
                 (and-left target-part proposal-part 'verdict)
                 state (covers 'upper state)))
          proposal-positive
          (fn [source destination]
            (app (function/const*
                  'mcmc/all-pairs-positive-member-sound [zero-level])
                 element 'proposal enum enum
                 (and-right target-part proposal-part 'verdict)
                 source destination
                 (covers 'upper source) (covers 'upper destination)))]
      (app (function/const* 'mcmc/nnrat-hastings-canonical-kernel-positive
                            [zero-level])
           element states 'target 'proposal (index-decide 'upper)
           'left 'right
           (target-positive 'left)
           (proposal-positive 'left 'right)
           (target-positive 'right)
           (proposal-positive 'right 'left))))})

(def index-one-step-reachable-spec
  "The n = 1 witness for the coming exists-n reachability definition: from any
  state, one step of the actual mass iterator started at the certified point
  mass puts positive mass on every state."
  {:name 'mcmc/nnrat-hastings-index-one-step-reachable-of-full-support
   :universes []
   :type
   (function/forall
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (eq-bool (full-support-decision0 (index-of 'upper) (index-finset 'upper)
                                      'target 'proposal)
               true-value)]
     ['selected (index-of 'upper)] ['destination (index-of 'upper)]]
    (positive
     (app (function/const* 'markov/nnrat-kernel-iterate [zero-level])
          (index-of 'upper) (index-finset 'upper)
          (canonical-kernel (index-of 'upper) (index-finset 'upper)
                            'target 'proposal (index-decide 'upper))
          (succ nat-zero)
          (function/lam
           [['state (index-of 'upper)]]
           (app (function/const* 'markov/nnrat-point-mass [zero-level])
                (index-of 'upper) (index-decide 'upper) 'selected 'state))
          'destination)))
   :value
   (function/lam
    [['upper nat]
     ['target (function/arrow (index-of 'upper) nnrat)]
     ['proposal (function/arrow (index-of 'upper) (index-of 'upper) nnrat)]
     ['verdict
      (eq-bool (full-support-decision0 (index-of 'upper) (index-finset 'upper)
                                      'target 'proposal)
               true-value)]
     ['selected (index-of 'upper)] ['destination (index-of 'upper)]]
    (app (function/const*
          'markov/nnrat-kernel-iterate-one-point-mass-positive [zero-level])
         (index-of 'upper) (index-finset 'upper) (index-decide 'upper)
         (canonical-kernel (index-of 'upper) (index-finset 'upper)
                           'target 'proposal (index-decide 'upper))
         (app (function/const* 'finite/index-certified-exhaustive-carrier [])
              'upper)
         'selected 'destination
         (app (function/const*
               'mcmc/nnrat-hastings-index-canonical-kernel-positive-of-full-support
               [])
              'upper 'target 'proposal 'verdict 'selected 'destination)))})

(def definition-specs
  [decide-positive-spec all-positive-spec all-pairs-positive-spec
   full-support-decision-spec])
(def theorem-specs
  [decide-positive-true-sound-spec
   all-positive-member-sound-spec
   all-pairs-member-sound-spec
   index-kernel-positive-spec
   index-one-step-reachable-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.logic.boolean-and rainbow.math.finite.index-hastings rainbow.math.finite.markov-point-mass rainbow.math.finite.markov-hastings-positive])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :finite-markov-full-support (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.markov-full-support))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
