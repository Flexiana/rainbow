(ns rainbow.math.nat.metric
  "Constructive order laws for computational natural distance."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
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

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- equality [left right]
  (function/equality type-level nat left right))

(defn- transitive [left middle right first second]
  (function/app (function/const* 'equality/transitive [type-level])
                nat left middle right first second))

(defn- symmetric [left right same]
  (function/app (function/const* 'equality/symmetric [type-level])
                nat left right same))

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(def distance-first-bound-spec
  {:name 'nat/distance-first-bound
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]]
    (at-most 'left (add (distance 'left 'right) 'right)))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (let [middle (add (distance 'right 'left) 'right)
          finish (add (distance 'left 'right) 'right)
          ordered
          (function/app (function/const* 'nat/distance-left-bound [])
                        'right 'left)
          rewrite-distance
          (congruent
           (function/lam [['value nat]] (add 'value 'right))
           (distance 'right 'left) (distance 'left 'right)
           (function/app
            (function/const* 'nat/distance-commutative []) 'right 'left))]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat
       (function/lam [['extra nat]]
                     (equality (add 'left 'extra) middle))
       (at-most 'left finish)
       ordered
       (function/lam
        [['extra nat] ['same (equality (add 'left 'extra) middle)]]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['candidate-extra nat]]
                       (equality (add 'left 'candidate-extra) finish))
         'extra
         (transitive (add 'left 'extra) middle finish
                     'same rewrite-distance))))))})

(def distance-upper-add-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (at-most (distance 'left 'right) (add 'left 'right))))]
    {:name 'nat/distance-upper-add
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (at-most (distance 'left 'right) (add 'left 'right)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app (function/const* 'nat/at-most-reflexive []) 'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]]
        (function/lam
         [['right nat]]
         (function/app
          (function/const* 'data/Nat.rec [zero-level])
          (function/lam
           [['candidate nat]]
           (at-most
            (distance (succ 'left-previous) 'candidate)
            (add (succ 'left-previous) 'candidate)))
          (let [finish (add (succ 'left-previous) zero)]
            (function/app
             (function/const* 'proposition/witness [type-level])
             nat
             (function/lam
              [['extra nat]]
              (equality (add (succ 'left-previous) 'extra) finish))
             zero
             (function/app (function/const* 'equality/reflexive [type-level])
                           nat finish)))
          (function/lam
           [['right-previous nat]
            ['ignored
             (at-most
              (distance (succ 'left-previous) 'right-previous)
              (add (succ 'left-previous) 'right-previous))]]
           (let [distance-previous
                 (distance 'left-previous 'right-previous)
                 sum-previous (add 'left-previous 'right-previous)
                 sum-successors
                 (add (succ 'left-previous) (succ 'right-previous))]
             (function/app
              (function/const* 'nat/at-most-transitive [])
              distance-previous sum-previous sum-successors
              (function/app 'induction-hypothesis 'right-previous)
              (function/app
               (function/const* 'nat/add-monotone [])
               'left-previous (succ 'left-previous)
               'right-previous (succ 'right-previous)
               (function/app (function/const* 'nat/at-most-successor [])
                             'left-previous)
               (function/app (function/const* 'nat/at-most-successor [])
                             'right-previous)))))
          'right)))
       'left))}))

(def distance-triangle-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['middle nat] ['right nat]]
          (at-most
           (distance 'left 'right)
           (add (distance 'left 'middle)
                (distance 'middle 'right)))))]
    {:name 'nat/distance-triangle
     :universes []
     :type
     (function/forall
      [['left nat] ['middle nat] ['right nat]]
      (at-most
       (distance 'left 'right)
       (add (distance 'left 'middle) (distance 'middle 'right))))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['middle nat] ['right nat]]
        (function/app (function/const* 'nat/distance-right-bound [])
                      'middle 'right))
       (function/lam
        [['left-previous nat]
         ['induction-hypothesis (function/app motive 'left-previous)]]
        (function/lam
         [['middle nat]]
         (function/app
          (function/const* 'data/Nat.rec [zero-level])
          (function/lam
           [['candidate nat]]
           (function/forall
            [['right nat]]
            (at-most
             (distance (succ 'left-previous) 'right)
             (add (distance (succ 'left-previous) 'candidate)
                  (distance 'candidate 'right)))))
          (function/lam
           [['right nat]]
           (function/app (function/const* 'nat/distance-upper-add [])
                         (succ 'left-previous) 'right))
          (function/lam
           [['middle-previous nat]
            ['ignored-middle
             (function/forall
              [['right nat]]
              (at-most
               (distance (succ 'left-previous) 'right)
               (add (distance (succ 'left-previous) 'middle-previous)
                    (distance 'middle-previous 'right))))]]
           (function/lam
            [['right nat]]
            (function/app
             (function/const* 'data/Nat.rec [zero-level])
             (function/lam
              [['candidate nat]]
              (at-most
               (distance (succ 'left-previous) 'candidate)
               (add
                (distance (succ 'left-previous) (succ 'middle-previous))
                (distance (succ 'middle-previous) 'candidate))))
             (let [distance-previous
                   (distance 'left-previous 'middle-previous)
                   middle (add distance-previous 'middle-previous)
                   finish (add distance-previous (succ 'middle-previous))
                   ordered
                   (function/app
                    (function/const* 'nat/distance-first-bound [])
                    'left-previous 'middle-previous)]
               (function/app
                (function/const* 'proposition/use-witness [type-level])
                nat
                (function/lam
                 [['extra nat]]
                 (equality (add 'left-previous 'extra) middle))
                (at-most (succ 'left-previous) finish)
                ordered
                (function/lam
                 [['extra nat]
                  ['same (equality (add 'left-previous 'extra) middle)]]
                 (let [start (add (succ 'left-previous) 'extra)
                       successor-middle (succ middle)
                       lift-same
                       (congruent
                        (function/lam [['value nat]] (succ 'value))
                        (add 'left-previous 'extra) middle 'same)
                       expose-successor
                       (symmetric
                        finish successor-middle
                        (function/app
                         (function/const* 'algebra/nat-add-successor-right [])
                         distance-previous 'middle-previous))]
                   (function/app
                    (function/const* 'proposition/witness [type-level])
                    nat
                    (function/lam
                     [['candidate-extra nat]]
                     (equality (add (succ 'left-previous) 'candidate-extra)
                               finish))
                    'extra
                    (transitive start successor-middle finish
                                lift-same expose-successor))))))
             (function/lam
              [['right-previous nat]
               ['ignored-right
                (at-most
                 (distance (succ 'left-previous) 'right-previous)
                 (add
                  (distance (succ 'left-previous)
                            (succ 'middle-previous))
                  (distance (succ 'middle-previous) 'right-previous)))]]
              (function/app 'induction-hypothesis
                            'middle-previous 'right-previous))
             'right)))
          'middle)))
       'left))}))

(def theorem-specs
  [distance-first-bound-spec distance-upper-add-spec distance-triangle-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat metric expression failed elaboration"
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
          {:origin :native :producer :constructive-nat-metric}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat metric theorem was rejected"
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
  (module/install-module checked-environment 'rainbow.math.nat.metric))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
