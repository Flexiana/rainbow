(ns rainbow.algorithms.proofs.general-descent
  "The general descent skeleton over signed rationals: the parent of the whole
  descent family. A step delegates to three pluggable functions -- a direction
  `direction(point)`, a step length `step-size(point)`, and an update rule
  `update(point, step, direction)` -- and composes them into the next point. Every
  concrete descent method (gradient descent, momentum, Newton, ...) is this
  skeleton with particular plug-ins (AHoF O13). The skeleton is proved once;
  instances reuse its unfold and iterate recurrence."
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
(def direction-type (function/arrow signed signed))
(def step-size-type (function/arrow signed nnrat))
(def update-type (function/arrow signed nnrat signed signed))

(defn- succ [value] (function/app (function/const* 'data/succ []) value))
(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- descent-step [direction step-size update point]
  (function/app (function/const* 'optimization/general-descent-step [])
                direction step-size update point))
(defn- descent-iterate [direction step-size update steps initial]
  (function/app (function/const* 'optimization/general-descent-iterate [])
                direction step-size update steps initial))

;; Definitions --------------------------------------------------------------

(def descent-step-spec
  {:name 'optimization/general-descent-step :kind :definition :universes []
   :type (function/forall [['direction direction-type]
                           ['step-size step-size-type]
                           ['update update-type]
                           ['point signed]]
                          signed)
   :value (function/lam [['direction direction-type]
                         ['step-size step-size-type]
                         ['update update-type]
                         ['point signed]]
                        (function/app 'update 'point
                                      (function/app 'step-size 'point)
                                      (function/app 'direction 'point)))})

(def descent-iterate-spec
  {:name 'optimization/general-descent-iterate :kind :definition :universes []
   :type (function/forall [['direction direction-type]
                           ['step-size step-size-type]
                           ['update update-type]]
                          (function/arrow nat signed signed))
   :value (function/lam [['direction direction-type]
                         ['step-size step-size-type]
                         ['update update-type]
                         ['steps nat] ['initial signed]]
                        (function/app
                         (function/const* 'data/Nat.rec [type-level])
                         (function/lam [['ignored nat]] signed)
                         'initial
                         (function/lam
                          [['step-index nat] ['previous signed]]
                          (descent-step 'direction 'step-size 'update
                                        'previous))
                         'steps))})

(def definition-specs [descent-step-spec descent-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def descent-step-unfold-spec
  {:name 'optimization/general-descent-step-unfold :universes []
   :type (function/forall [['direction direction-type]
                           ['step-size step-size-type]
                           ['update update-type]
                           ['point signed]]
                          (equality signed
                                    (descent-step 'direction 'step-size
                                                  'update 'point)
                                    (function/app
                                     'update 'point
                                     (function/app 'step-size 'point)
                                     (function/app 'direction 'point))))
   :value (function/lam [['direction direction-type]
                         ['step-size step-size-type]
                         ['update update-type]
                         ['point signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (descent-step 'direction 'step-size
                                              'update 'point)))})

(def descent-iterate-zero-spec
  {:name 'optimization/general-descent-iterate-zero :universes []
   :type (function/forall [['direction direction-type]
                           ['step-size step-size-type]
                           ['update update-type]
                           ['initial signed]]
                          (equality signed
                                    (descent-iterate 'direction 'step-size
                                                     'update
                                                     (function/const*
                                                      'data/zero [])
                                                     'initial)
                                    'initial))
   :value (function/lam [['direction direction-type]
                         ['step-size step-size-type]
                         ['update update-type]
                         ['initial signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed 'initial))})

(def descent-iterate-successor-spec
  (let [step (function/lam
              [['step-index nat] ['previous signed]]
              (descent-step 'direction 'step-size 'update 'previous))
        previous (descent-iterate 'direction 'step-size 'update
                                  'steps 'initial)
        next (descent-iterate 'direction 'step-size 'update
                              (succ 'steps) 'initial)]
    {:name 'optimization/general-descent-iterate-successor :universes []
     :type (function/forall [['direction direction-type]
                             ['step-size step-size-type]
                             ['update update-type]
                             ['steps nat] ['initial signed]]
                            (equality signed next
                                      (function/app step 'steps previous)))
     :value (function/lam [['direction direction-type]
                           ['step-size step-size-type]
                           ['update update-type]
                           ['steps nat] ['initial signed]]
                          (function/app
                           (function/const*
                            'nat/recursor-successor-constant [zero-level])
                           signed 'initial step 'steps))}))

(def theorem-specs
  [descent-step-unfold-spec descent-iterate-zero-spec
   descent-iterate-successor-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "General-descent expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :general-descent}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "General-descent declaration rejected"
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
