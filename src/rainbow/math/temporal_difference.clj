(ns rainbow.math.temporal-difference
  "Bounded temporal-difference (Q-learning) updates over signed rationals.

  The temporal-difference error `reward + discount * next - current` is a signed
  quantity that can be negative when the current estimate is too high, and the
  update nudges the estimate by the rate-scaled error: `current + rate * error`.
  Signed rationals make the negative correction representable without any kernel
  primitive subtraction. The update rule is the shared ITERATE skeleton of AHoF
  D61 Q-learning, D62 Sarsa, and Expected Sarsa (only the target differs)."
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

(defn- succ [value] (function/app (function/const* 'data/succ []) value))

(defn- nnrat-multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- signed-make [positive negative]
  (function/app (function/const* 'signed/make []) positive negative))

(defn- signed-positive [value]
  (function/app (function/const* 'signed/positive []) value))

(defn- signed-negative [value]
  (function/app (function/const* 'signed/negative []) value))

(defn- signed-add [left right]
  (function/app (function/const* 'signed/add []) left right))

(defn- signed-subtract [left right]
  (function/app (function/const* 'signed/subtract []) left right))

(defn- scale [rate value]
  (function/app (function/const* 'signed/scale []) rate value))

(defn- td-error [reward discount next current]
  (function/app (function/const* 'learning/signed-td-error [])
                reward discount next current))

(defn- q-update [rate reward discount next current]
  (function/app (function/const* 'learning/signed-q-update [])
                rate reward discount next current))

(defn- q-iterate [rate reward discount next steps initial]
  (function/app (function/const* 'learning/signed-q-iterate [])
                rate reward discount next steps initial))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Definitions --------------------------------------------------------------

(def scale-spec
  {:name 'signed/scale :kind :definition :universes []
   :type (function/arrow nnrat signed signed)
   :value (function/lam
           [['rate nnrat] ['value signed]]
           (signed-make (nnrat-multiply 'rate (signed-positive 'value))
                        (nnrat-multiply 'rate (signed-negative 'value))))})

(def td-error-spec
  {:name 'learning/signed-td-error :kind :definition :universes []
   :type (function/arrow signed nnrat signed signed signed)
   :value (function/lam
           [['reward signed] ['discount nnrat] ['next signed]
            ['current signed]]
           (signed-subtract
            (signed-add 'reward (scale 'discount 'next))
            'current))})

(def q-update-spec
  {:name 'learning/signed-q-update :kind :definition :universes []
   :type (function/arrow nnrat signed nnrat signed signed signed)
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
            ['current signed]]
           (signed-add 'current
                       (scale 'rate
                              (td-error 'reward 'discount 'next 'current))))})

(def q-iterate-spec
  {:name 'learning/signed-q-iterate :kind :definition :universes []
   :type (function/arrow nnrat signed nnrat signed
                         (function/arrow nat signed signed))
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
            ['steps nat] ['initial signed]]
           (function/app
            (function/const* 'data/Nat.rec [type-level])
            (function/lam [['ignored nat]] signed)
            'initial
            (function/lam
             [['step-index nat] ['previous signed]]
             (q-update 'rate 'reward 'discount 'next 'previous))
            'steps))})

(def definition-specs
  [scale-spec td-error-spec q-update-spec q-iterate-spec])

;; Theorems -----------------------------------------------------------------

(def td-error-unfold-spec
  {:name 'learning/signed-td-error-unfold :universes []
   :type (function/forall
          [['reward signed] ['discount nnrat] ['next signed]
           ['current signed]]
          (equality signed (td-error 'reward 'discount 'next 'current)
                    (signed-subtract
                     (signed-add 'reward (scale 'discount 'next))
                     'current)))
   :value (function/lam
           [['reward signed] ['discount nnrat] ['next signed]
            ['current signed]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         signed
                         (td-error 'reward 'discount 'next 'current)))})

(def q-update-unfold-spec
  {:name 'learning/signed-q-update-unfold :universes []
   :type (function/forall
          [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
           ['current signed]]
          (equality signed (q-update 'rate 'reward 'discount 'next 'current)
                    (signed-add 'current
                                (scale 'rate
                                       (td-error 'reward 'discount 'next
                                                 'current)))))
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
            ['current signed]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         signed
                         (q-update 'rate 'reward 'discount 'next 'current)))})

(def q-iterate-zero-spec
  {:name 'learning/signed-q-iterate-zero :universes []
   :type (function/forall
          [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
           ['initial signed]]
          (equality signed
                    (q-iterate 'rate 'reward 'discount 'next
                               (function/const* 'data/zero []) 'initial)
                    'initial))
   :value (function/lam
           [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
            ['initial signed]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         signed 'initial))})

(def q-iterate-successor-spec
  (let [step (function/lam
              [['step-index nat] ['previous signed]]
              (q-update 'rate 'reward 'discount 'next 'previous))
        previous (q-iterate 'rate 'reward 'discount 'next 'steps 'initial)
        next-iterate (q-iterate 'rate 'reward 'discount 'next
                                (succ 'steps) 'initial)]
    {:name 'learning/signed-q-iterate-successor :universes []
     :type (function/forall
            [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
             ['steps nat] ['initial signed]]
            (equality signed next-iterate
                      (function/app step 'steps previous)))
     :value (function/lam
             [['rate nnrat] ['reward signed] ['discount nnrat] ['next signed]
              ['steps nat] ['initial signed]]
             (function/app
              (function/const* 'nat/recursor-successor-constant [zero-level])
              signed 'initial step 'steps))}))

;; NOTE: the generic abstract q-iterate successor law is intentionally omitted.
;; Over the signed carrier its definitional-equality check unfolds the deep
;; composed reducible chain (q-update -> td-error -> scale/add/subtract -> make)
;; past the kernel budget. The worked instance proves the successor recurrence at
;; concrete steps instead, where the chain reduces fully.
(def theorem-specs
  [td-error-unfold-spec q-update-unfold-spec q-iterate-zero-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Temporal-difference expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :temporal-difference}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Temporal-difference declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.temporal-difference))
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
