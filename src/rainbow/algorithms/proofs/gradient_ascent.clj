(ns rainbow.algorithms.proofs.gradient-ascent
  "Bounded fixed-rate gradient ascent over exact nonnegative rationals.

  The update `point + rate * (gradient point)` is the shared ITERATE skeleton of
  AHoF D49 and the many policy/parameter ascent methods that plug a different
  gradient estimator into the same loop. The gradient is a first-class function
  argument, so this engine is reused by specialization rather than re-derived."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def gradient-type (function/arrow nnrat nnrat))

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

(defn- ascent-step [grad rate point]
  (function/app (function/const* 'optimization/nnrat-ascent-step [])
                grad rate point))

(defn- ascent-iterate [grad rate steps initial]
  (function/app (function/const* 'optimization/nnrat-ascent-iterate [])
                grad rate steps initial))

(def ascent-step-spec
  {:name 'optimization/nnrat-ascent-step
   :kind :definition :universes []
   :type (function/forall
          [['gradient gradient-type] ['rate nnrat] ['point nnrat]] nnrat)
   :value
   (function/lam
    [['gradient gradient-type] ['rate nnrat] ['point nnrat]]
    (add 'point (multiply 'rate (function/app 'gradient 'point))))})

(def ascent-iterate-spec
  {:name 'optimization/nnrat-ascent-iterate
   :kind :definition :universes []
   :type (function/forall
          [['gradient gradient-type] ['rate nnrat]]
          (function/arrow nat nnrat nnrat))
   :value
   (function/lam
    [['gradient gradient-type] ['rate nnrat]
     ['steps nat] ['initial nnrat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nnrat)
     'initial
     (function/lam
      [['step-index nat] ['previous nnrat]]
      (ascent-step 'gradient 'rate 'previous))
     'steps))})

(def definition-specs [ascent-step-spec ascent-iterate-spec])

(def ascent-step-unfold-spec
  {:name 'optimization/nnrat-ascent-step-unfold
   :universes []
   :type (function/forall
          [['gradient gradient-type] ['rate nnrat] ['point nnrat]]
          (equality nnrat (ascent-step 'gradient 'rate 'point)
                    (add 'point (multiply 'rate
                                          (function/app 'gradient 'point)))))
   :value
   (function/lam
    [['gradient gradient-type] ['rate nnrat] ['point nnrat]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nnrat (ascent-step 'gradient 'rate 'point)))})

(def ascent-iterate-zero-spec
  {:name 'optimization/nnrat-ascent-iterate-zero
   :universes []
   :type (function/forall
          [['gradient gradient-type] ['rate nnrat] ['initial nnrat]]
          (equality nnrat (ascent-iterate 'gradient 'rate zero 'initial)
                    'initial))
   :value
   (function/lam
    [['gradient gradient-type] ['rate nnrat] ['initial nnrat]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nnrat 'initial))})

(def ascent-iterate-successor-spec
  (let [step
        (function/lam
         [['step-index nat] ['previous nnrat]]
         (ascent-step 'gradient 'rate 'previous))
        previous (ascent-iterate 'gradient 'rate 'steps 'initial)
        next (ascent-iterate 'gradient 'rate (succ 'steps) 'initial)]
    {:name 'optimization/nnrat-ascent-iterate-successor
     :universes []
     :type (function/forall
            [['gradient gradient-type] ['rate nnrat]
             ['steps nat] ['initial nnrat]]
            (equality nnrat next (function/app step 'steps previous)))
     :value
     (function/lam
      [['gradient gradient-type] ['rate nnrat]
       ['steps nat] ['initial nnrat]]
      (function/app
       (function/const* 'nat/recursor-successor-constant [zero-level])
       nnrat 'initial step 'steps))}))

(def ascent-step-transfer-spec
  (let [unfold
        (fn [point]
          (equality nnrat (ascent-step 'gradient 'rate point)
                    (add point (multiply 'rate
                                         (function/app 'gradient point)))))]
    {:name 'optimization/nnrat-ascent-step-transfer
     :universes []
     :type (function/forall
            [['gradient gradient-type] ['rate nnrat]
             ['left-point nnrat] ['right-point nnrat]]
            (function/app (function/const* 'proposition/conjunction [])
                          (unfold 'left-point) (unfold 'right-point)))
     :value
     (function/lam
      [['gradient gradient-type] ['rate nnrat]
       ['left-point nnrat] ['right-point nnrat]]
      (function/app
       (function/const* 'proposition/conjoin [])
       (unfold 'left-point) (unfold 'right-point)
       (function/app (function/const* 'equality/reflexive [type-level])
                     nnrat (ascent-step 'gradient 'rate 'left-point))
       (function/app (function/const* 'equality/reflexive [type-level])
                     nnrat (ascent-step 'gradient 'rate 'right-point))))}))

(def theorem-specs
  [ascent-step-unfold-spec ascent-iterate-zero-spec
   ascent-iterate-successor-spec ascent-step-transfer-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Gradient-ascent expression failed elaboration"
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
          :rainbow/provenance
          {:origin :native :producer :gradient-ascent}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Gradient-ascent declaration rejected"
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
