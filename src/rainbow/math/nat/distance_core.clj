(ns rainbow.math.nat.distance-core
  "Constructive zero and identity laws for computational natural distance."
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

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- reflexive [value]
  (function/app (function/const* 'equality/reflexive [type-level])
                nat value))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))

(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(defn- impossible [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))

(def distance-zero-left-spec
  {:name 'nat/distance-zero-left
   :universes []
   :type
   (function/forall
    [['value nat]]
    (equality (distance zero 'value) 'value))
   :value
   (function/lam
    [['value nat]]
    (reflexive 'value))})

(def distance-zero-right-spec
  {:name 'nat/distance-zero-right
   :universes []
   :type
   (function/forall
    [['value nat]]
    (equality (distance 'value zero) 'value))
   :value
   (function/lam
    [['value nat]]
    (function/app
     (function/const* 'nat/distance-commutative [])
     'value zero))})

(def distance-self-spec
  (let [motive
        (function/lam
         [['value nat]]
         (equality (distance 'value 'value) zero))]
    {:name 'nat/distance-self
     :universes []
     :type
     (function/forall
      [['value nat]]
      (equality (distance 'value 'value) zero))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (reflexive zero)
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        'induction-hypothesis)
       'value))}))

(def equal-of-distance-zero-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat :implicit]
           ['same (equality (distance 'left 'right) zero)]]
          (equality 'left 'right)))]
    {:name 'nat/equal-of-distance-zero
     :universes []
     :type
     (function/forall
      [['left nat :implicit] ['right nat :implicit]
       ['same (equality (distance 'left 'right) zero)]]
      (equality 'left 'right))
     :value
     (function/lam
      [['left nat :implicit]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat :implicit]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/forall
           [['same (equality (distance zero 'candidate) zero)]]
           (equality zero 'candidate)))
         (function/lam
          [['same (equality zero zero)]]
          'same)
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['same (equality (distance zero 'right-previous) zero)]]
             (equality zero 'right-previous))]
           ['same (equality (succ 'right-previous) zero)]]
          (impossible
           (equality zero (succ 'right-previous))
           (function/app
            (function/const* 'nat/zero-not-successor [])
            'right-previous
            (symmetric (succ 'right-previous) zero 'same))))
         'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]
         ['right nat :implicit]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (function/forall
           [['same
             (equality
              (distance (succ 'left-previous) 'candidate)
              zero)]]
           (equality (succ 'left-previous) 'candidate)))
         (function/lam
          [['same (equality (succ 'left-previous) zero)]]
          (impossible
           (equality (succ 'left-previous) zero)
           (function/app
            (function/const* 'nat/zero-not-successor [])
            'left-previous
            (symmetric (succ 'left-previous) zero 'same))))
         (function/lam
          [['right-previous nat]
           ['ignored
            (function/forall
             [['same
               (equality
                (distance (succ 'left-previous) 'right-previous)
                zero)]]
             (equality (succ 'left-previous) 'right-previous))]
           ['same
            (equality
             (distance (succ 'left-previous) (succ 'right-previous))
             zero)]]
          (congruent
           (function/lam [['candidate nat]] (succ 'candidate))
           'left-previous 'right-previous
           (function/app
            'induction-hypothesis 'right-previous 'same)))
         'right))
       'left))}))

(def distance-zero-of-equal-spec
  {:name 'nat/distance-zero-of-equal
   :universes []
   :type
   (function/forall
    [['left nat :implicit] ['right nat :implicit]
     ['same (equality 'left 'right)]]
    (equality (distance 'left 'right) zero))
   :value
   (function/lam
    [['left nat :implicit] ['right nat :implicit]
     ['same (equality 'left 'right)]]
    (let [self-distance (distance 'left 'left)
          original-distance (distance 'left 'right)
          rewrite-to-self
          (symmetric
           self-distance original-distance
           (congruent
            (function/lam
             [['candidate nat]]
             (distance 'left 'candidate))
            'left 'right 'same))]
      (transitive
       original-distance self-distance zero
       rewrite-to-self
       (function/app
        (function/const* 'nat/distance-self [])
        'left))))})

(def distance-zero-equivalent-equal-spec
  {:name 'nat/distance-zero-equivalent-equal
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]]
    (proposition/equivalence
     (equality (distance 'left 'right) zero)
     (equality 'left 'right)))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (let [distance-is-zero (equality (distance 'left 'right) zero)
          values-are-equal (equality 'left 'right)]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       distance-is-zero values-are-equal
       (function/lam
        [['same distance-is-zero]]
        (function/app
         (function/const* 'nat/equal-of-distance-zero [])
         'left 'right 'same))
       (function/lam
        [['same values-are-equal]]
        (function/app
         (function/const* 'nat/distance-zero-of-equal [])
         'left 'right 'same)))))})

(def theorem-specs
  [distance-zero-left-spec
   distance-zero-right-spec
   distance-self-spec
   equal-of-distance-zero-spec
   distance-zero-of-equal-spec
   distance-zero-equivalent-equal-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat distance core expression failed elaboration"
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
           :producer :constructive-nat-distance-core}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat distance core theorem was rejected"
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
  (module/install-module checked-environment 'rainbow.math.nat.distance-core))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
