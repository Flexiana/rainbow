(ns rainbow.math.nat.metric-separation
  "Constructive positivity and separation laws for computational Nat distance."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))

(defn- succ [value]
  (function/app successor value))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- unequal [left right]
  (proposition/negation (equality left right)))

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat value))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))

(defn- impossible [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))

(def positive-of-nonzero-spec
  (let [motive
        (function/lam
         [['value nat]]
         (function/forall
          [['nonzero (unequal 'value zero)]]
          (below zero 'value)))]
    {:name 'nat/positive-of-nonzero
     :universes []
     :type
     (function/forall
      [['value nat :implicit] ['nonzero (unequal 'value zero)]]
      (below zero 'value))
     :value
     (function/lam
      [['value nat :implicit]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['nonzero (unequal zero zero)]]
        (impossible
         (below zero zero)
         (function/app 'nonzero (reflexive zero))))
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]
         ['nonzero (unequal (succ 'previous) zero)]]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam
          [['extra nat]]
          (equality (add (succ zero) 'extra) (succ 'previous)))
         'previous
         (reflexive (succ 'previous))))
       'value))}))

(def nonzero-of-positive-spec
  (let [motive
        (function/lam
         [['value nat]]
         (function/forall
          [['positive (below zero 'value)]]
          (unequal 'value zero)))]
    {:name 'nat/nonzero-of-positive
     :universes []
     :type
     (function/forall
      [['value nat :implicit] ['positive (below zero 'value)]]
      (unequal 'value zero))
     :value
     (function/lam
      [['value nat :implicit]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['positive (below zero zero)]
         ['same (equality zero zero)]]
        (function/app
         (function/const* 'proposition/use-witness [type-level])
         nat
         (function/lam
          [['extra nat]]
          (equality (add (succ zero) 'extra) zero))
         (proposition/falsity)
         'positive
         (function/lam
          [['extra nat]
           ['successor-is-zero
            (equality (add (succ zero) 'extra) zero)]]
          (function/app
           (function/const* 'nat/zero-not-successor [])
           'extra
           (symmetric (succ 'extra) zero 'successor-is-zero)))))
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]
         ['positive (below zero (succ 'previous))]
         ['successor-is-zero (equality (succ 'previous) zero)]]
        (function/app
         (function/const* 'nat/zero-not-successor [])
         'previous
         (symmetric (succ 'previous) zero 'successor-is-zero)))
       'value))}))

(def distance-nonzero-of-not-equal-spec
  {:name 'nat/distance-nonzero-of-not-equal
   :universes []
   :type
   (function/forall
    [['left nat :implicit] ['right nat :implicit]
     ['different (unequal 'left 'right)]]
    (unequal (distance 'left 'right) zero))
   :value
   (function/lam
    [['left nat :implicit] ['right nat :implicit]
     ['different (unequal 'left 'right)]
     ['distance-is-zero (equality (distance 'left 'right) zero)]]
    (function/app
     'different
     (function/app
      (function/const* 'nat/equal-of-distance-zero [])
      'left 'right 'distance-is-zero)))})

(def distance-positive-of-not-equal-spec
  {:name 'nat/distance-positive-of-not-equal
   :universes []
   :type
   (function/forall
    [['left nat :implicit] ['right nat :implicit]
     ['different (unequal 'left 'right)]]
    (below zero (distance 'left 'right)))
   :value
   (function/lam
    [['left nat :implicit] ['right nat :implicit]
     ['different (unequal 'left 'right)]]
    (function/app
     (function/const* 'nat/positive-of-nonzero [])
     (distance 'left 'right)
     (function/app
      (function/const* 'nat/distance-nonzero-of-not-equal [])
      'left 'right 'different)))})

(def distance-positive-equivalent-not-equal-spec
  {:name 'nat/distance-positive-equivalent-not-equal
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]]
    (proposition/equivalence
     (below zero (distance 'left 'right))
     (unequal 'left 'right)))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (let [positive (below zero (distance 'left 'right))
          different (unequal 'left 'right)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       positive different
       (function/lam
        [['distance-is-positive positive]
         ['same (equality 'left 'right)]]
        (function/app
         (function/const* 'nat/nonzero-of-positive [])
         (distance 'left 'right) 'distance-is-positive
         (function/app
          (function/const* 'nat/distance-zero-of-equal [])
          'left 'right 'same)))
       (function/lam
        [['values-differ different]]
        (function/app
         (function/const* 'nat/distance-positive-of-not-equal [])
         'left 'right 'values-differ)))))})

(def theorem-specs
  [positive-of-nonzero-spec
   nonzero-of-positive-spec
   distance-nonzero-of-not-equal-spec
   distance-positive-of-not-equal-spec
   distance-positive-equivalent-not-equal-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat metric-separation expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency :opaque
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native
           :producer :constructive-nat-metric-separation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat metric-separation theorem was rejected"
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
  (module/install-module checked-environment 'rainbow.math.nat.metric-separation))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
