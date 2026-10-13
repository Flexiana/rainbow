(ns rainbow.math.rational.signed.equivalence-laws
  "Symmetry and negation transport for Grothendieck-pair signed equivalence."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def signed (function/const* 'signed/SignedRational []))

(defn- positive [value]
  (function/app (function/const* 'signed/positive []) value))

(defn- negative [value]
  (function/app (function/const* 'signed/negative []) value))

(defn- negate [value]
  (function/app (function/const* 'signed/negate []) value))

(defn- nnrat-add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- nnrat-equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- signed-equivalent [left right]
  (function/app (function/const* 'signed/equivalent []) left right))

(defn- nnrat-equivalent-transitive [left middle right first second]
  (function/app (function/const* 'nnrat/equivalent-transitive [])
                left middle right first second))

(def equivalent-symmetric-spec
  {:name 'signed/equivalent-symmetric
   :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (signed-equivalent 'right 'left))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (function/app
     (function/const* 'nnrat/equivalent-symmetric [])
     (nnrat-add (positive 'left) (negative 'right))
     (nnrat-add (positive 'right) (negative 'left))
     'same))})

(def negate-respects-equivalence-spec
  {:name 'signed/negate-respects-equivalence
   :universes []
   :type
   (function/forall
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (signed-equivalent (negate 'left) (negate 'right)))
   :value
   (function/lam
    [['left signed] ['right signed]
     ['same (signed-equivalent 'left 'right)]]
    (let [left-positive (positive 'left)
          left-negative (negative 'left)
          right-positive (positive 'right)
          right-negative (negative 'right)
          start (nnrat-add left-negative right-positive)
          first (nnrat-add right-positive left-negative)
          second (nnrat-add left-positive right-negative)
          finish (nnrat-add right-negative left-positive)
          commute-start
          (function/app (function/const* 'nnrat/add-commutative [])
                        left-negative right-positive)
          reverse-original
          (function/app (function/const* 'signed/equivalent-symmetric [])
                        'left 'right 'same)
          commute-finish
          (function/app (function/const* 'nnrat/add-commutative [])
                        left-positive right-negative)]
      (nnrat-equivalent-transitive
       start first finish commute-start
       (nnrat-equivalent-transitive
        first second finish reverse-original commute-finish))))})

(def theorem-specs
  [equivalent-symmetric-spec negate-respects-equivalence-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Signed equivalence law failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind :theorem
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :signed-equivalence-laws}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Signed equivalence law was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.signed.equivalence-laws))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
