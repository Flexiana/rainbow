(ns rainbow.algorithms.proofs.gradient-descent
  "Bounded fixed-rate gradient descent over signed rationals.

  Descent subtracts the rate-scaled gradient from the current signed point:
  `point - from-nnrat(rate * gradient point)`. Subtraction is the signed-rational
  (addition-only) construction, so descent trajectories can pass through zero and
  become negative without the kernel needing primitive subtraction. This is the
  descent counterpart of the gradient-ascent engine and the simplest instance of
  the operations-research descent pattern (AHoF O17)."
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

(defn- succ [value] (function/app (function/const* 'data/succ []) value))

(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- from-nnrat [value]
  (function/app (function/const* 'signed/from-nnrat []) value))

(defn- signed-subtract [left right]
  (function/app (function/const* 'signed/subtract []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- descent-step [rate gradient point]
  (function/app (function/const* 'optimization/signed-descent-step [])
                rate gradient point))

(defn- descent-iterate [rate gradient steps initial]
  (function/app (function/const* 'optimization/signed-descent-iterate [])
                rate gradient steps initial))

;; Definitions --------------------------------------------------------------

(def descent-step-spec
  {:name 'optimization/signed-descent-step
   :kind :definition :universes []
   :type (function/forall [['rate nnrat] ['gradient gradient-type]
                           ['point signed]]
                          signed)
   :value (function/lam [['rate nnrat] ['gradient gradient-type]
                         ['point signed]]
                        (signed-subtract
                         'point
                         (from-nnrat (nnrat-multiply
                                      'rate
                                      (function/app 'gradient 'point)))))})

(def descent-iterate-spec
  {:name 'optimization/signed-descent-iterate
   :kind :definition :universes []
   :type (function/forall [['rate nnrat] ['gradient gradient-type]]
                          (function/arrow nat signed signed))
   :value (function/lam [['rate nnrat] ['gradient gradient-type]
                         ['steps nat] ['initial signed]]
                        (function/app
                         (function/const* 'data/Nat.rec [type-level])
                         (function/lam [['ignored nat]] signed)
                         'initial
                         (function/lam
                          [['step-index nat] ['previous signed]]
                          (descent-step 'rate 'gradient 'previous))
                         'steps))})

(def definition-specs [descent-step-spec descent-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def descent-step-unfold-spec
  {:name 'optimization/signed-descent-step-unfold
   :universes []
   :type (function/forall [['rate nnrat] ['gradient gradient-type]
                           ['point signed]]
                          (equality signed
                                    (descent-step 'rate 'gradient 'point)
                                    (signed-subtract
                                     'point
                                     (from-nnrat
                                      (nnrat-multiply
                                       'rate
                                       (function/app 'gradient 'point))))))
   :value (function/lam [['rate nnrat] ['gradient gradient-type]
                         ['point signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed (descent-step 'rate 'gradient 'point)))})

(def descent-iterate-zero-spec
  {:name 'optimization/signed-descent-iterate-zero
   :universes []
   :type (function/forall [['rate nnrat] ['gradient gradient-type]
                           ['initial signed]]
                          (equality signed
                                    (descent-iterate 'rate 'gradient
                                                     (function/const*
                                                      'data/zero [])
                                                     'initial)
                                    'initial))
   :value (function/lam [['rate nnrat] ['gradient gradient-type]
                         ['initial signed]]
                        (function/app
                         (function/const* 'equality/reflexive [type-level])
                         signed 'initial))})

(def descent-iterate-successor-spec
  (let [step (function/lam
              [['step-index nat] ['previous signed]]
              (descent-step 'rate 'gradient 'previous))
        previous (descent-iterate 'rate 'gradient 'steps 'initial)
        next (descent-iterate 'rate 'gradient (succ 'steps) 'initial)]
    {:name 'optimization/signed-descent-iterate-successor
     :universes []
     :type (function/forall [['rate nnrat] ['gradient gradient-type]
                             ['steps nat] ['initial signed]]
                            (equality signed next
                                      (function/app step 'steps previous)))
     :value (function/lam [['rate nnrat] ['gradient gradient-type]
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
      (throw (ex-info "Gradient-descent expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :gradient-descent}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Gradient-descent declaration rejected"
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
  (module/install-module checked-environment 'rainbow.algorithms.proofs.gradient-descent))
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
