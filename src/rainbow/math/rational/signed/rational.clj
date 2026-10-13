(ns rainbow.math.rational.signed.rational
  "Signed rationals as proof data: a pair (positive, negative) of nonnegative
  rationals denoting positive - negative. Subtraction is expressed with nnrat
  addition only, so the kernel never needs a primitive subtraction and the
  nonnegative-rational machinery is reused directly. Equivalence is the
  Grothendieck relation (p1,n1) ~ (p2,n2) iff p1 + n2 ~ p2 + n1, again additive.

  This unlocks signed differences (e.g. value of information, descent updates)
  while keeping every kernel reduction inside the existing exact-rational base."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))
(def nnrat-one (function/const* 'nnrat/one []))

(def raw-signed
  (function/app (function/const* 'data/Product [type-level type-level])
                nnrat nnrat))

(def signed (function/const* 'signed/SignedRational []))

(defn- pair [positive negative]
  (function/app (function/const* 'data/pair [type-level type-level])
                nnrat nnrat positive negative))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- nnrat-at-most [left right]
  (function/app (function/const* 'nnrat/at-most []) left right))

(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- positive [value]
  (function/app (function/const* 'signed/positive []) value))

(defn- negative [value]
  (function/app (function/const* 'signed/negative []) value))

(defn- make [positive negative]
  (function/app (function/const* 'signed/make []) positive negative))

(defn- equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- equality [carrier left right]
  (function/equality type-level carrier left right))

;; Definitions --------------------------------------------------------------

(def carrier-spec
  {:name 'signed/SignedRational :kind :definition :universes []
   :type [:sort type-level] :value raw-signed})

(def make-spec
  {:name 'signed/make :kind :definition :universes []
   :type (function/arrow nnrat nnrat signed)
   :value (function/lam [['positive nnrat] ['negative nnrat]]
                        (pair 'positive 'negative))})

(def positive-spec
  {:name 'signed/positive :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['value signed]]
                        (function/app
                         (function/const* 'product/first
                                          [type-level type-level])
                         nnrat nnrat 'value))})

(def negative-spec
  {:name 'signed/negative :kind :definition :universes []
   :type (function/arrow signed nnrat)
   :value (function/lam [['value signed]]
                        (function/app
                         (function/const* 'product/second
                                          [type-level type-level])
                         nnrat nnrat 'value))})

(def from-nnrat-spec
  {:name 'signed/from-nnrat :kind :definition :universes []
   :type (function/arrow nnrat signed)
   :value (function/lam [['value nnrat]] (make 'value nnrat-zero))})

(def zero-spec
  {:name 'signed/zero :kind :definition :universes []
   :type signed :value (make nnrat-zero nnrat-zero)})

(def one-spec
  {:name 'signed/one :kind :definition :universes []
   :type signed :value (make nnrat-one nnrat-zero)})

(def add-spec-def
  {:name 'signed/add :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam
           [['left signed] ['right signed]]
           (make (nnrat-add (positive 'left) (positive 'right))
                 (nnrat-add (negative 'left) (negative 'right))))})

(def negate-spec
  {:name 'signed/negate :kind :definition :universes []
   :type (function/arrow signed signed)
   :value (function/lam [['value signed]]
                        (make (negative 'value) (positive 'value)))})

(def subtract-spec
  {:name 'signed/subtract :kind :definition :universes []
   :type (function/arrow signed signed signed)
   :value (function/lam
           [['left signed] ['right signed]]
           (make (nnrat-add (positive 'left) (negative 'right))
                 (nnrat-add (negative 'left) (positive 'right))))})

(def equivalent-spec
  {:name 'signed/equivalent :kind :definition :universes []
   :type (function/arrow signed signed 'Prop)
   :value (function/lam
           [['left signed] ['right signed]]
           (nnrat-equivalent
            (nnrat-add (positive 'left) (negative 'right))
            (nnrat-add (positive 'right) (negative 'left))))})

(def nonnegative-spec
  {:name 'signed/nonnegative :kind :definition :universes []
   :type (function/arrow signed 'Prop)
   :value (function/lam [['value signed]]
                        (nnrat-at-most (negative 'value) (positive 'value)))})

(def definition-specs
  [carrier-spec make-spec positive-spec negative-spec from-nnrat-spec
   zero-spec one-spec add-spec-def negate-spec subtract-spec
   equivalent-spec nonnegative-spec])

;; Theorems -----------------------------------------------------------------

(def positive-of-make-spec
  {:name 'signed/positive-of-make :universes []
   :type (function/forall [['positive nnrat] ['negative nnrat]]
                          (equality nnrat (positive (make 'positive 'negative))
                                    'positive))
   :value (function/lam [['positive nnrat] ['negative nnrat]]
                        (function/app (function/const* 'equality/reflexive
                                                       [type-level])
                                      nnrat 'positive))})

(def negative-of-make-spec
  {:name 'signed/negative-of-make :universes []
   :type (function/forall [['positive nnrat] ['negative nnrat]]
                          (equality nnrat (negative (make 'positive 'negative))
                                    'negative))
   :value (function/lam [['positive nnrat] ['negative nnrat]]
                        (function/app (function/const* 'equality/reflexive
                                                       [type-level])
                                      nnrat 'negative))})

(def subtract-unfold-spec
  {:name 'signed/subtract-unfold :universes []
   :type (function/forall
          [['left signed] ['right signed]]
          (equality signed
                    (function/app (function/const* 'signed/subtract [])
                                  'left 'right)
                    (make (nnrat-add (positive 'left) (negative 'right))
                          (nnrat-add (negative 'left) (positive 'right)))))
   :value (function/lam
           [['left signed] ['right signed]]
           (function/app (function/const* 'equality/reflexive [type-level])
                         signed
                         (function/app (function/const* 'signed/subtract [])
                                       'left 'right)))})

(def equivalent-reflexive-spec
  {:name 'signed/equivalent-reflexive :universes []
   :type (function/forall [['value signed]] (equivalent 'value 'value))
   :value (function/lam
           [['value signed]]
           (function/app (function/const* 'nnrat/equivalent-reflexive [])
                         (nnrat-add (positive 'value) (negative 'value))))})

(def theorem-specs
  [positive-of-make-spec negative-of-make-spec subtract-unfold-spec
   equivalent-reflexive-spec])

;; Environment plumbing -----------------------------------------------------

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Signed-rational expression failed elaboration"
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
          :rainbow/provenance {:origin :native :producer :signed-rational}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Signed-rational declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.rational.signed.rational))
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
