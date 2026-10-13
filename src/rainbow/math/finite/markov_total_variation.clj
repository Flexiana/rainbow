(ns rainbow.math.finite.markov-total-variation
  "Total-variation distance between finite exact-rational distributions, and
  the separation half of the coming ergodic theorem.

  The ergodic-hypotheses bundle is packaged and discharged by computation; the
  theorem those hypotheses exist for still is not stated. Its classical proof
  runs through a metric on distributions, and this module is the bridgehead:
  the L1 distance over the enumeration -- the sum of pointwise exact distances
  -- with the lemmas that make ZERO distance mean something.

  What is proved: the distance is a congruence for pointwise equivalence
  (the rewrite that turns TV(mu K, nu K) into TV(mu, nu) under
  stationarity); it is symmetric; it vanishes on pointwise-
  equivalent distributions; and -- the load-bearing direction -- a vanishing
  distance forces pointwise equivalence AT EVERY ENUMERATED STATE, through a
  new generic lemma that a zero finite sum has zero listed terms. The capstone
  packages the separation half of uniqueness: two stationary distributions at
  total-variation zero agree pointwise on the carrier.

  What is deliberately NOT here, so nobody reads the bridgehead as the bridge:
  no contraction inequality. The classical Dobrushin step -- one kernel
  application shrinks this distance by a factor below one under the certified
  positive minimum -- is the single remaining inequality between these lemmas
  and stationary-distribution uniqueness, and it is unproved. The reduction is
  the point: uniqueness now rests on exactly one named open inequality rather
  than on a theory that did not exist. Native and axiom-free on D63."
  (:require [rainbow.module :as module]
            [rainbow.environment :as environment]
            [rainbow.math.finite.markov-stationarity :as stationarity]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.nnrat.add-zero-split :as add-zero-split]
            [rainbow.math.rational.nnrat.map-sum-respects :as map-sum-respects]
            [rainbow.math.rational.nnrat.metric-separation :as metric-separation]
            [rainbow.math.logic.proposition :as proposition]))

(def U [:param 'u])
(def data-u [:succ U])
(def type-u [:sort data-u])
(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- app [f & xs] (apply function/app f xs))
(defn- list-of [element]
  (app (function/const* 'data/List [data-u]) element))
(defn- exact-finset-of [element]
  (app (function/const* 'finset-data/Finset [U]) element))
(defn- enumeration [element source]
  (app (function/const* 'finset-data/enumeration [U]) element source))
(defn- membership [element items value]
  (app (function/const* 'list/membership [U]) element items value))
(defn- req [left right]
  (app (function/const* 'nnrat/equivalent []) left right))
(defn- map-sum [element mapping items]
  (app (function/const* 'nnrat/map-sum [U]) element mapping items))
(defn- rdistance [left right]
  (app (function/const* 'nnrat/distance []) left right))
(defn- radd [left right]
  (app (function/const* 'nnrat/add []) left right))
(defn- mass-type [element] (function/arrow element nnrat))
(defn- equivalent-transitive [x y z pxy pyz]
  (app (function/const* 'nnrat/equivalent-transitive []) x y z pxy pyz))
(defn- equivalent-symmetric [x y proof]
  (app (function/const* 'nnrat/equivalent-symmetric []) x y proof))

(def total-variation-spec
  {:name 'markov/nnrat-total-variation :kind :definition :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]]
    nnrat)
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]]
    (map-sum 'S
             (function/lam [['state 'S]]
                           (rdistance (app 'left 'state) (app 'right 'state)))
             (enumeration 'S 'states)))})

(defn- total-variation [element states left right]
  (app (function/const* 'markov/nnrat-total-variation [U])
       element states left right))

;; ---- a zero finite sum has zero listed terms --------------------------------

(def map-sum-zero-of-member-spec
  "Generic and reusable: if the finite sum is equivalent to zero, every LISTED
  term is. List induction; at each cons the zero splits across the addition by
  the existing add-zero-split pair, the head case transports along the
  membership equality, and the tail case is the hypothesis."
  {:name 'nnrat/map-sum-zero-of-member :universes ['u]
   :type
   (function/forall
    [['A type-u] ['f (function/arrow 'A nnrat)] ['items (list-of 'A)]]
    (function/arrow
     (req (map-sum 'A 'f 'items) nnrat-zero)
     (function/forall
      [['value 'A] ['member (membership 'A 'items 'value)]]
      (req (app 'f 'value) nnrat-zero))))
   :value
   (function/lam
    [['A type-u] ['f (function/arrow 'A nnrat)] ['items (list-of 'A)]]
    (app
     (function/const* 'data/List.rec [data-u zero-level])
     'A
     (function/lam
      [['current (list-of 'A)]]
      (function/arrow
       (req (map-sum 'A 'f 'current) nnrat-zero)
       (function/forall
        [['value 'A] ['member (membership 'A 'current 'value)]]
        (req (app 'f 'value) nnrat-zero))))
     (function/lam
      [['whole (req (map-sum 'A 'f
                             (app (function/const* 'data/nil [data-u]) 'A))
                    nnrat-zero)]
       ['value 'A] ['member (proposition/falsity)]]
      (app (function/const* 'proposition/explode [])
           (req (app 'f 'value) nnrat-zero) 'member))
     (function/lam
      [['head 'A] ['tail (list-of 'A)]
       ['tail-sound
        (function/arrow
         (req (map-sum 'A 'f 'tail) nnrat-zero)
         (function/forall
          [['value 'A] ['member (membership 'A 'tail 'value)]]
          (req (app 'f 'value) nnrat-zero)))]
       ['whole (req (radd (app 'f 'head) (map-sum 'A 'f 'tail)) nnrat-zero)]
       ['value 'A]
       ['member
        (proposition/disjunction
         (function/equality data-u 'A 'value 'head)
         (membership 'A 'tail 'value))]]
      (app
       (function/const* 'proposition/use-disjunction [])
       (function/equality data-u 'A 'value 'head)
       (membership 'A 'tail 'value)
       (req (app 'f 'value) nnrat-zero)
       'member
       (function/lam
        [['same (function/equality data-u 'A 'value 'head)]]
        (app (function/const* 'equality/reverse-substitution [data-u])
             'A 'value 'head 'same
             (function/lam [['other 'A]] (req (app 'f 'other) nnrat-zero))
             (app (function/const* 'nnrat/add-zero-split-left [])
                  (app 'f 'head) (map-sum 'A 'f 'tail) 'whole)))
       (function/lam
        [['rest (membership 'A 'tail 'value)]]
        (app 'tail-sound
             (app (function/const* 'nnrat/add-zero-split-right [])
                  (app 'f 'head) (map-sum 'A 'f 'tail) 'whole)
             'value 'rest))))
     'items))})

;; ---- the metric laws that matter --------------------------------------------

(def total-variation-symmetric-spec
  {:name 'markov/nnrat-total-variation-symmetric :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]]
    (req (total-variation 'S 'states 'left 'right)
         (total-variation 'S 'states 'right 'left)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]]
    (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
         'S
         (function/lam [['state 'S]]
                       (rdistance (app 'left 'state) (app 'right 'state)))
         (function/lam [['state 'S]]
                       (rdistance (app 'right 'state) (app 'left 'state)))
         (function/lam [['state 'S]]
                       (app (function/const* 'nnrat/distance-symmetric [])
                            (app 'left 'state) (app 'right 'state)))
         (enumeration 'S 'states)))})

(def total-variation-respects-pointwise-spec
  "Congruence: total variation respects pointwise equivalence of its two
  mass arguments. This is the rewrite the ergodic assembly needs to turn
  TV(mu K, nu K) into TV(mu, nu) under stationarity before the contraction
  inequality can bite; each summand transports along the new distance
  congruence, and the sum follows pointwise."
  {:name 'markov/nnrat-total-variation-respects-pointwise-equivalent
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['equivalent-left (mass-type 'S)]
     ['right (mass-type 'S)] ['equivalent-right (mass-type 'S)]
     ['agree-left (function/forall
                   [['state 'S]]
                   (req (app 'left 'state) (app 'equivalent-left 'state)))]
     ['agree-right (function/forall
                    [['state 'S]]
                    (req (app 'right 'state) (app 'equivalent-right 'state)))]]
    (req (total-variation 'S 'states 'left 'right)
         (total-variation 'S 'states 'equivalent-left 'equivalent-right)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['equivalent-left (mass-type 'S)]
     ['right (mass-type 'S)] ['equivalent-right (mass-type 'S)]
     ['agree-left (function/forall
                   [['state 'S]]
                   (req (app 'left 'state) (app 'equivalent-left 'state)))]
     ['agree-right (function/forall
                    [['state 'S]]
                    (req (app 'right 'state) (app 'equivalent-right 'state)))]]
    (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
         'S
         (function/lam [['state 'S]]
                       (rdistance (app 'left 'state) (app 'right 'state)))
         (function/lam [['state 'S]]
                       (rdistance (app 'equivalent-left 'state)
                                  (app 'equivalent-right 'state)))
         (function/lam [['state 'S]]
                       (app (function/const*
                             'nnrat/distance-respects-equivalence [])
                            (app 'left 'state) (app 'equivalent-left 'state)
                            (app 'right 'state) (app 'equivalent-right 'state)
                            (app 'agree-left 'state)
                            (app 'agree-right 'state)))
         (enumeration 'S 'states)))})

(def total-variation-zero-of-pointwise-spec
  {:name 'markov/nnrat-total-variation-zero-of-pointwise-equivalent
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['agree (function/forall [['state 'S]]
                              (req (app 'left 'state) (app 'right 'state)))]]
    (req (total-variation 'S 'states 'left 'right) nnrat-zero))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['agree (function/forall [['state 'S]]
                              (req (app 'left 'state) (app 'right 'state)))]]
    (equivalent-transitive
     (total-variation 'S 'states 'left 'right)
     (map-sum 'S (function/lam [['state 'S]] nnrat-zero)
              (enumeration 'S 'states))
     nnrat-zero
     (app (function/const* 'nnrat/map-sum-respects-equivalence [U])
          'S
          (function/lam [['state 'S]]
                        (rdistance (app 'left 'state) (app 'right 'state)))
          (function/lam [['state 'S]] nnrat-zero)
          (function/lam [['state 'S]]
                        (app (function/const* 'nnrat/distance-zero-of-equivalent [])
                             (app 'left 'state) (app 'right 'state)
                             (app 'agree 'state)))
          (enumeration 'S 'states))
     (app (function/const* 'nnrat/map-sum-zero [U])
          'S (enumeration 'S 'states))))})

(def total-variation-separates-spec
  "The load-bearing direction: vanishing total variation forces pointwise
  equivalence at every enumerated state -- zero sum gives zero listed distance,
  and the metric separation iff turns a zero distance into equivalence."
  {:name 'markov/nnrat-total-variation-zero-implies-pointwise-equivalent
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['vanishes (req (total-variation 'S 'states 'left 'right) nnrat-zero)]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (req (app 'left 'state) (app 'right 'state)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['vanishes (req (total-variation 'S 'states 'left 'right) nnrat-zero)]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (let [zero-distance (req (rdistance (app 'left 'state) (app 'right 'state))
                             nnrat-zero)
          agreement (req (app 'left 'state) (app 'right 'state))]
      (app
       (app (function/const* 'proposition/left [])
            (function/arrow zero-distance agreement)
            (function/arrow agreement zero-distance)
            (app (function/const* 'nnrat/distance-zero-iff-equivalent [])
                 (app 'left 'state) (app 'right 'state)))
       (app (function/const* 'nnrat/map-sum-zero-of-member [U])
            'S
            (function/lam [['other 'S]]
                          (rdistance (app 'left 'other) (app 'right 'other)))
            (enumeration 'S 'states)
            'vanishes
            'state 'member))))})

(def stationary-separation-spec
  "The separation half of ergodic uniqueness, packaged: two stationary
  distributions at total-variation zero agree pointwise on the carrier. The
  stationarity hypotheses are carried so the statement composes directly with
  the one open Dobrushin inequality named in the docstring, whose conclusion
  is exactly the `vanishes` premise here."
  {:name 'markov/nnrat-stationary-pointwise-unique-of-total-variation-zero
   :universes ['u]
   :type
   (function/forall
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['left-stationary
      (app (function/const* 'markov/nnrat-stationary [U])
           'S 'states 'kernel 'left)]
     ['right-stationary
      (app (function/const* 'markov/nnrat-stationary [U])
           'S 'states 'kernel 'right)]
     ['vanishes (req (total-variation 'S 'states 'left 'right) nnrat-zero)]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (req (app 'left 'state) (app 'right 'state)))
   :value
   (function/lam
    [['S type-u] ['states (exact-finset-of 'S)]
     ['kernel (function/arrow 'S 'S nnrat)]
     ['left (mass-type 'S)] ['right (mass-type 'S)]
     ['left-stationary
      (app (function/const* 'markov/nnrat-stationary [U])
           'S 'states 'kernel 'left)]
     ['right-stationary
      (app (function/const* 'markov/nnrat-stationary [U])
           'S 'states 'kernel 'right)]
     ['vanishes (req (total-variation 'S 'states 'left 'right) nnrat-zero)]
     ['state 'S]
     ['member (membership 'S (enumeration 'S 'states) 'state)]]
    (app (function/const*
          'markov/nnrat-total-variation-zero-implies-pointwise-equivalent [U])
         'S 'states 'left 'right 'vanishes 'state 'member))})

(def definition-specs [total-variation-spec])
(def theorem-specs
  [map-sum-zero-of-member-spec
   total-variation-respects-pointwise-spec
   total-variation-symmetric-spec
   total-variation-zero-of-pointwise-spec
   total-variation-separates-spec
   stationary-separation-spec])

(defn- require-alias [checked-environment alias]
  (when-not (environment/resolve-id checked-environment alias)
    (throw (ex-info "total-variation chain is missing an alias"
                    {:missing alias})))
  checked-environment)

(defn- extend-if-missing
  "Chains overlap here: two upstream worlds both carry the six known verbatim
  duplicate identities, and extending both into one environment is an alias
  conflict at add time -- the exact second-proof hazard the design notes record. Each
  auxiliary chain is therefore entered only if its marker alias is absent."
  [checked-environment marker extend]
  (if (environment/resolve-id checked-environment marker)
    checked-environment
    (extend checked-environment)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.finite.markov-stationarity])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (extend-if-missing 'nnrat/add-zero-split-left add-zero-split/extend-environment) (extend-if-missing 'nnrat/map-sum-respects-equivalence map-sum-respects/extend-environment) (extend-if-missing 'nnrat/distance-zero-iff-equivalent metric-separation/extend-environment) (require-alias 'nnrat/map-sum-zero) (require-alias 'nnrat/equivalent-transitive) (support/extend-with :finite-markov-total-variation (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.markov-total-variation))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
