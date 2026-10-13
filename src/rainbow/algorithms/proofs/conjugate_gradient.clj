(ns rainbow.algorithms.proofs.conjugate-gradient
  "Conjugate gradient descent over signed rationals with pair-valued state. The
  state carries a position and a search direction. Each step forms a new
  direction from the current negative gradient plus beta times the remembered
  previous direction, `d' = -gradient(x) + beta * d`, then moves the position
  `x' = x + alpha * d'`. The remembered direction is the closure-with-memory that
  distinguishes conjugate gradient from plain steepest descent (AHoF O18); the
  separate step size alpha distinguishes it from momentum.

  Scope (measured by the kernel): this module has 3 definitional unfoldings (true by unfolding a definition).
  None of its theorems is a guarantee about the algorithm for all inputs; `lein verify rainbow.algorithms.proofs.conjugate-gradient`
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
(def gradient-type (function/arrow signed signed))
(def state (function/app (function/const* 'data/Product [type-level type-level])
                         signed signed))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))
(defn- signed-negate [value]
  (function/app (function/const* 'signed/negate []) value))
(defn- signed-scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))
(defn- position [s]
  (function/app (function/const* 'product/first [type-level type-level])
                signed signed s))
(defn- direction [s]
  (function/app (function/const* 'product/second [type-level type-level])
                signed signed s))
(defn- state-pair [x d]
  (function/app (function/const* 'data/pair [type-level type-level])
                signed signed x d))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- conjugate-direction [beta gradient x d]
  (function/app (function/const* 'optimization/conjugate-direction [])
                beta gradient x d))
(defn- conjugate-step [alpha beta gradient s]
  (function/app (function/const* 'optimization/conjugate-step [])
                alpha beta gradient s))
(defn- conjugate-iterate [alpha beta gradient steps initial]
  (function/app (function/const* 'optimization/conjugate-iterate [])
                alpha beta gradient steps initial))

;; Definitions --------------------------------------------------------------

(def conjugate-direction-spec
  {:name 'optimization/conjugate-direction :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['gradient gradient-type]
                           ['x signed] ['d signed]]
                          signed)
   :value (function/lam [['beta nnrat] ['gradient gradient-type]
                         ['x signed] ['d signed]]
                        (signed-add
                         (signed-negate (function/app 'gradient 'x))
                         (signed-scale 'beta 'd)))})

(def conjugate-step-spec
  {:name 'optimization/conjugate-step :kind :definition :universes []
   :type (function/forall [['alpha nnrat] ['beta nnrat]
                           ['gradient gradient-type] ['s state]]
                          state)
   :value (function/lam [['alpha nnrat] ['beta nnrat]
                         ['gradient gradient-type] ['s state]]
                        (state-pair
                         (signed-add
                          (position 's)
                          (signed-scale 'alpha
                                        (conjugate-direction 'beta 'gradient
                                                             (position 's)
                                                             (direction 's))))
                         (conjugate-direction 'beta 'gradient
                                              (position 's) (direction 's))))})

(def conjugate-iterate-spec
  {:name 'optimization/conjugate-iterate :kind :definition :universes []
   :type (function/forall [['alpha nnrat] ['beta nnrat]
                           ['gradient gradient-type]]
                          (function/arrow nat state state))
   :value (function/lam [['alpha nnrat] ['beta nnrat]
                         ['gradient gradient-type]
                         ['steps nat] ['initial state]]
                        (function/app
                         (function/const* 'data/Nat.rec [type-level])
                         (function/lam [['ignored nat]] state)
                         'initial
                         (function/lam
                          [['step-index nat] ['previous state]]
                          (conjugate-step 'alpha 'beta 'gradient 'previous))
                         'steps))})

(def definition-specs
  [conjugate-direction-spec conjugate-step-spec conjugate-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def conjugate-direction-unfold-spec
  {:name 'optimization/conjugate-direction-unfold :universes []
   :type (function/forall [['beta nnrat] ['gradient gradient-type]
                           ['x signed] ['d signed]]
                          (equality signed
                                    (conjugate-direction 'beta 'gradient 'x 'd)
                                    (signed-add
                                     (signed-negate
                                      (function/app 'gradient 'x))
                                     (signed-scale 'beta 'd))))
   :value (function/lam [['beta nnrat] ['gradient gradient-type]
                         ['x signed] ['d signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (conjugate-direction 'beta 'gradient 'x 'd)))})

(def conjugate-step-unfold-spec
  {:name 'optimization/conjugate-step-unfold :universes []
   :type (function/forall [['alpha nnrat] ['beta nnrat]
                           ['gradient gradient-type] ['s state]]
                          (equality state
                                    (conjugate-step 'alpha 'beta 'gradient 's)
                                    (state-pair
                                     (signed-add
                                      (position 's)
                                      (signed-scale
                                       'alpha
                                       (conjugate-direction 'beta 'gradient
                                                            (position 's)
                                                            (direction 's))))
                                     (conjugate-direction 'beta 'gradient
                                                          (position 's)
                                                          (direction 's)))))
   :value (function/lam [['alpha nnrat] ['beta nnrat]
                         ['gradient gradient-type] ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (conjugate-step 'alpha 'beta 'gradient 's)))})

(def conjugate-iterate-zero-spec
  {:name 'optimization/conjugate-iterate-zero :universes []
   :type (function/forall [['alpha nnrat] ['beta nnrat]
                           ['gradient gradient-type] ['initial state]]
                          (equality state
                                    (conjugate-iterate 'alpha 'beta 'gradient
                                                       (function/const*
                                                        'data/zero [])
                                                       'initial)
                                    'initial))
   :value (function/lam [['alpha nnrat] ['beta nnrat]
                         ['gradient gradient-type] ['initial state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state 'initial))})

(def theorem-specs
  [conjugate-direction-unfold-spec conjugate-step-unfold-spec
   conjugate-iterate-zero-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Conjugate-gradient expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :conjugate-gradient}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Conjugate-gradient declaration rejected"
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
