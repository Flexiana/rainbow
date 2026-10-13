(ns rainbow.algorithms.proofs.momentum
  "Polyak momentum descent over signed rationals with pair-valued state.

  The state is a Product of a signed position and a signed velocity. Each step
  updates the velocity `v' = beta * v - alpha * gradient(position)` (the momentum
  term `beta * v` accumulates past steps, which plain gradient descent lacks) and
  then the position `x' = x + v'`. Velocity carry uses signed scaling and
  subtraction; the state is read and rebuilt through the Product projections.
  This is the first optimizer that evolves paired state (AHoF O19), wrapping the
  signed-descent gradient with velocity accumulation."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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

(defn- momentum-velocity [beta rate gradient x v]
  (function/app (function/const* 'optimization/momentum-velocity [])
                beta rate gradient x v))
(defn- momentum-step [beta rate gradient s]
  (function/app (function/const* 'optimization/momentum-step [])
                beta rate gradient s))
(defn- momentum-iterate [beta rate gradient steps initial]
  (function/app (function/const* 'optimization/momentum-iterate [])
                beta rate gradient steps initial))

;; Definitions --------------------------------------------------------------

(def momentum-velocity-spec
  {:name 'optimization/momentum-velocity :kind :definition :universes []
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
                          (nnrat-multiply 'rate
                                          (function/app 'gradient 'x)))))})

(def momentum-step-spec
  {:name 'optimization/momentum-step :kind :definition :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['s state]]
                          state)
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['s state]]
                        (state-pair
                         (signed-add
                          (position 's)
                          (momentum-velocity 'beta 'rate 'gradient
                                             (position 's) (velocity 's)))
                         (momentum-velocity 'beta 'rate 'gradient
                                            (position 's) (velocity 's))))})

(def momentum-iterate-spec
  {:name 'optimization/momentum-iterate :kind :definition :universes []
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
                          (momentum-step 'beta 'rate 'gradient 'previous))
                         'steps))})

(def definition-specs
  [momentum-velocity-spec momentum-step-spec momentum-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def momentum-velocity-unfold-spec
  {:name 'optimization/momentum-velocity-unfold :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type]
                           ['x signed] ['v signed]]
                          (equality signed
                                    (momentum-velocity 'beta 'rate 'gradient
                                                       'x 'v)
                                    (signed-subtract
                                     (signed-scale 'beta 'v)
                                     (from-nnrat
                                      (nnrat-multiply
                                       'rate
                                       (function/app 'gradient 'x))))))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type]
                         ['x signed] ['v signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (momentum-velocity 'beta 'rate 'gradient
                                                   'x 'v)))})

;; A step rebuilds the state as [x + v', v'] with the new velocity v'.
(def momentum-step-unfold-spec
  {:name 'optimization/momentum-step-unfold :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['s state]]
                          (equality state
                                    (momentum-step 'beta 'rate 'gradient 's)
                                    (state-pair
                                     (signed-add
                                      (position 's)
                                      (momentum-velocity 'beta 'rate 'gradient
                                                         (position 's)
                                                         (velocity 's)))
                                     (momentum-velocity 'beta 'rate 'gradient
                                                        (position 's)
                                                        (velocity 's)))))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['s state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state (momentum-step 'beta 'rate 'gradient 's)))})

(def momentum-iterate-zero-spec
  {:name 'optimization/momentum-iterate-zero :universes []
   :type (function/forall [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type] ['initial state]]
                          (equality state
                                    (momentum-iterate 'beta 'rate 'gradient
                                                      (function/const*
                                                       'data/zero [])
                                                      'initial)
                                    'initial))
   :value (function/lam [['beta nnrat] ['rate nnrat]
                         ['gradient gradient-type] ['initial state]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         state 'initial))})

(def momentum-iterate-successor-spec
  (let [step (function/lam
              [['step-index nat] ['previous state]]
              (momentum-step 'beta 'rate 'gradient 'previous))
        previous (momentum-iterate 'beta 'rate 'gradient 'steps 'initial)
        next (momentum-iterate 'beta 'rate 'gradient (succ 'steps) 'initial)]
    {:name 'optimization/momentum-iterate-successor :universes []
     :type (function/forall [['beta nnrat] ['rate nnrat]
                             ['gradient gradient-type]
                             ['steps nat] ['initial state]]
                            (equality state next
                                      (function/app step 'steps previous)))
     :value (function/lam [['beta nnrat] ['rate nnrat]
                           ['gradient gradient-type]
                           ['steps nat] ['initial state]]
                          (function/app
                           (function/const*
                            'nat/recursor-successor-constant [zero-level])
                           state 'initial step 'steps))}))

(def theorem-specs
  [momentum-velocity-unfold-spec momentum-step-unfold-spec
   momentum-iterate-zero-spec momentum-iterate-successor-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Momentum expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :momentum}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Momentum declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (concat definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.momentum))
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
