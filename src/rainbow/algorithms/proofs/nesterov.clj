(ns rainbow.algorithms.proofs.nesterov
  "Nesterov accelerated momentum over signed rationals with pair-valued state.

  Nesterov differs from Polyak momentum by evaluating the gradient at a
  look-ahead point `x + beta * v` rather than at `x`: the velocity update is
  `v' = beta * v - rate * gradient(x + beta * v)` and the position moves
  `x' = x + v'`. When the gradient depends on position the look-ahead genuinely
  changes the trajectory. This wraps the momentum pair-state engine (AHoF O20)
  with the look-ahead evaluation.

  Scope (measured by the kernel): this module has 4 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.nesterov`
  prints this classification."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))
(def gradient-type (function/arrow signed nnrat))
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))
(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-subtract [left right]
  (function/app (function/const* 'signed/subtract []) left right))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- position [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- velocity [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))
(defn- state-pair [x v]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x v))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- lookahead [beta x v]
  (function/app (function/const* 'optimization/nesterov-lookahead [])
                beta x v))
(defn- nesterov-velocity [beta rate gradient x v]
  (function/app (function/const* 'optimization/nesterov-velocity [])
                beta rate gradient x v))
(defn- nesterov-step [beta rate gradient s]
  (function/app (function/const* 'optimization/nesterov-step [])
                beta rate gradient s))
(defn- nesterov-iterate [beta rate gradient steps initial]
  (function/app (function/const* 'optimization/nesterov-iterate [])
                beta rate gradient steps initial))

;; Definitions --------------------------------------------------------------

(def lookahead-spec
  {:name 'optimization/nesterov-lookahead :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['x signed] ['v signed]] signed)
   :value (function/lam [['beta nnrat] ['x signed] ['v signed]]
                        (signed-add 'x (signed-scale 'beta 'v)))})

(def nesterov-velocity-spec
  {:name 'optimization/nesterov-velocity :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type]
                           ['x signed] ['v signed]]
                          signed)
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type]
                         ['x signed] ['v signed]]
                        (signed-subtract
                         (signed-scale 'beta 'v)
                         (from-nnrat
                          (nnrat-multiply
                           'rate
                           (function/app 'gradient
                                         (lookahead 'beta 'x 'v))))))})

(def nesterov-step-spec
  {:name 'optimization/nesterov-step :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['s state]]
                          state)
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['s state]]
                        (state-pair
                         (signed-add
                          (position 's)
                          (nesterov-velocity 'beta 'rate 'gradient
                                             (position 's) (velocity 's)))
                         (nesterov-velocity 'beta 'rate 'gradient
                                            (position 's) (velocity 's))))})

(def nesterov-iterate-spec
  {:name 'optimization/nesterov-iterate :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type]]
                          (function/arrow nat state state))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type]
                         ['steps nat] ['initial state]]
                        (function/app
                         (function/const* 'data/Nat.rec [type-level])
                         (function/lam [['ignored nat]] state)
                         'initial
                         (function/lam
                          [['step-index nat] ['previous state]]
                          (nesterov-step 'beta 'rate 'gradient 'previous))
                         'steps))})

(def definition-specs
  [lookahead-spec nesterov-velocity-spec nesterov-step-spec
   nesterov-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def lookahead-unfold-spec
  {:name 'optimization/nesterov-lookahead-unfold :universes []
   :type (function/forall [['beta nnrat] ['x signed] ['v signed]]
                          (equality signed
                                    (lookahead 'beta 'x 'v)
                                    (signed-add 'x (signed-scale 'beta 'v))))
   :value (function/lam [['beta nnrat] ['x signed] ['v signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (lookahead 'beta 'x 'v)))})

(def nesterov-velocity-unfold-spec
  {:name 'optimization/nesterov-velocity-unfold :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type]
                           ['x signed] ['v signed]]
                          (equality signed
                                    (nesterov-velocity 'beta 'rate 'gradient
                                                       'x 'v)
                                    (signed-subtract
                                     (signed-scale 'beta 'v)
                                     (from-nnrat
                                      (nnrat-multiply
                                       'rate
                                       (function/app
                                        'gradient
                                        (lookahead 'beta 'x 'v)))))))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type]
                         ['x signed] ['v signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (nesterov-velocity 'beta 'rate 'gradient
                                                   'x 'v)))})

(def nesterov-step-unfold-spec
  {:name 'optimization/nesterov-step-unfold :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['s state]]
                          (equality state
                                    (nesterov-step 'beta 'rate 'gradient 's)
                                    (state-pair
                                     (signed-add
                                      (position 's)
                                      (nesterov-velocity 'beta 'rate 'gradient
                                                         (position 's)
                                                         (velocity 's)))
                                     (nesterov-velocity 'beta 'rate 'gradient
                                                        (position 's)
                                                        (velocity 's)))))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (nesterov-step 'beta 'rate 'gradient 's)))})

(def nesterov-iterate-zero-spec
  {:name 'optimization/nesterov-iterate-zero :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['initial state]]
                          (equality state
                                    (nesterov-iterate 'beta 'rate 'gradient
                                                      (function/const*
                                                       'data/zero [])
                                                      'initial)
                                    'initial))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['initial state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state 'initial))})

;; The generic abstract-step successor recurrence (proved for the momentum and
;; general-descent engines via nat/recursor-successor-constant) is intentionally
;; omitted here: the look-ahead nesting makes the abstract-argument definitional
;; equality check exceed even a 16x kernel budget, and inflating the trusted
;; check budget for a single lemma is the wrong lever. The recurrence is instead
;; carried by the concrete worked steps in ahof-nesterov, which reduce fully and
;; stay well within budget.

(def theorem-specs
  [lookahead-unfold-spec nesterov-velocity-unfold-spec
   nesterov-step-unfold-spec nesterov-iterate-zero-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nesterov expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance {:origin :native :producer :nesterov}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nesterov declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (concat definition-specs theorem-specs)))

(defn definition-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        definition-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
