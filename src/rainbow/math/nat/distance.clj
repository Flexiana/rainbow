(ns rainbow.math.nat.distance
  "Computational natural distance and additive foreign-vocabulary bridges."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def V [:param 'v])
(def W [:param 'w])
(def type-u [:sort [:succ U]])
(def type-v [:sort [:succ V]])
(def type-w [:sort [:succ W]])
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

(defn- congruent [mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function [type-level type-level])
   nat nat mapping left right same))

(def heterogeneous-add-spec
  {:name 'algebra/heterogeneous-add
   :kind :definition
   :universes ['u 'v 'w]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['B type-v] ['C type-w]
     ['dictionary (function/arrow 'A 'B 'C)]]
    (function/arrow 'A 'B 'C))
   :value
   (function/lam
    [['A type-u] ['B type-v] ['C type-w]
     ['dictionary (function/arrow 'A 'B 'C)]]
    'dictionary)})

(def homogeneous-add-instance-spec
  {:name 'algebra/homogeneous-add-instance
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['dictionary (function/arrow 'A 'A 'A)]]
    (function/arrow 'A 'A 'A))
   :value
   (function/lam
    [['A type-u] ['dictionary (function/arrow 'A 'A 'A)]]
    'dictionary)})

(def nat-distance-spec
  {:name 'nat/distance
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] (function/arrow nat nat))
     (function/lam [['right nat]] 'right)
     (function/lam
      [['previous nat]
       ['previous-distance (function/arrow nat nat)]]
      (function/lam
       [['right nat]]
       (function/app
        (function/const* 'data/Nat.rec [type-level])
        (function/lam [['ignored nat]] nat)
        (succ 'previous)
        (function/lam
         [['right-previous nat] ['ignored nat]]
         (function/app 'previous-distance 'right-previous))
        'right)))
     'left))})

(def distance-successor-spec
  {:name 'nat/distance-successor
   :universes []
   :type
   (function/forall
    [['left nat :implicit] ['right nat :implicit]]
    (equality (distance (succ 'left) (succ 'right))
              (distance 'left 'right)))
   :value
   (function/lam
    [['left nat :implicit] ['right nat :implicit]]
    (function/app (function/const* 'equality/reflexive [type-level])
                  nat (distance 'left 'right)))})

(def distance-commutative-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (equality (distance 'left 'right)
                    (distance 'right 'left))))]
    {:name 'nat/distance-commutative
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (equality (distance 'left 'right) (distance 'right 'left)))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app
         (function/const* 'data/Nat.rec [zero-level])
         (function/lam
          [['candidate nat]]
          (equality (distance zero 'candidate)
                    (distance 'candidate zero)))
         (function/app (function/const* 'equality/reflexive [type-level])
                       nat zero)
         (function/lam
          [['right-previous nat]
           ['ignored
            (equality (distance zero 'right-previous)
                      (distance 'right-previous zero))]]
          (function/app (function/const* 'equality/reflexive [type-level])
                        nat (succ 'right-previous)))
         'right))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        (function/lam
         [['right nat]]
         (function/app
          (function/const* 'data/Nat.rec [zero-level])
          (function/lam
           [['candidate nat]]
           (equality (distance (succ 'previous) 'candidate)
                     (distance 'candidate (succ 'previous))))
          (function/app (function/const* 'equality/reflexive [type-level])
                        nat (succ 'previous))
          (function/lam
           [['right-previous nat]
            ['ignored
             (equality (distance (succ 'previous) 'right-previous)
                       (distance 'right-previous (succ 'previous)))]]
           (function/app 'induction-hypothesis 'right-previous))
          'right)))
       'left))}))

(def distance-add-left-spec
  (let [motive
        (function/lam
         [['prefix nat]]
         (function/forall
          [['left nat] ['right nat]]
          (equality
           (distance (add 'prefix 'left) (add 'prefix 'right))
           (distance 'left 'right))))]
    {:name 'nat/distance-add-left
     :universes []
     :type
     (function/forall
      [['prefix nat] ['left nat] ['right nat]]
      (equality
       (distance (add 'prefix 'left) (add 'prefix 'right))
       (distance 'left 'right)))
     :value
     (function/lam
      [['prefix nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['left nat] ['right nat]]
        (function/app (function/const* 'equality/reflexive [type-level])
                      nat (distance 'left 'right)))
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]
         ['left nat] ['right nat]]
        (function/app 'induction-hypothesis 'left 'right))
       'prefix))}))

(def distance-add-right-spec
  {:name 'nat/distance-add-right
   :universes []
   :type
   (function/forall
    [['left nat] ['suffix nat] ['right nat]]
    (equality
     (distance (add 'left 'suffix) (add 'right 'suffix))
     (distance 'left 'right)))
   :value
   (function/lam
    [['left nat] ['suffix nat] ['right nat]]
    (let [start (distance (add 'left 'suffix) (add 'right 'suffix))
          first-middle (distance (add 'suffix 'left)
                                 (add 'right 'suffix))
          second-middle (distance (add 'suffix 'left)
                                  (add 'suffix 'right))
          finish (distance 'left 'right)
          commute-left
          (congruent
           (function/lam
            [['value nat]] (distance 'value (add 'right 'suffix)))
           (add 'left 'suffix) (add 'suffix 'left)
           (function/app (function/const* 'nat/add-commutative [])
                         'left 'suffix))
          commute-right
          (congruent
           (function/lam
            [['value nat]] (distance (add 'suffix 'left) 'value))
           (add 'right 'suffix) (add 'suffix 'right)
           (function/app (function/const* 'nat/add-commutative [])
                         'right 'suffix))
          first-two
          (transitive start first-middle second-middle
                      commute-left commute-right)]
      (transitive
       start second-middle finish first-two
       (function/app (function/const* 'nat/distance-add-left [])
                     'suffix 'left 'right))))})

(def distance-right-bound-spec
  (let [motive
        (function/lam
         [['left nat]]
         (function/forall
          [['right nat]]
          (at-most 'right (add 'left (distance 'left 'right)))))]
    {:name 'nat/distance-right-bound
     :universes []
     :type
     (function/forall
      [['left nat] ['right nat]]
      (at-most 'right (add 'left (distance 'left 'right))))
     :value
     (function/lam
      [['left nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['right nat]]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['extra nat]]
                       (equality (add 'right 'extra) 'right))
         zero
         (function/app
          (function/const* 'algebra/nat-add-zero-right []) 'right)))
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
            'candidate
            (add (succ 'left-previous)
                 (distance (succ 'left-previous) 'candidate))))
          (let [finish
                (add (succ 'left-previous) (succ 'left-previous))]
            (function/app
             (function/const* 'proposition/witness [type-level])
             nat
             (function/lam [['extra nat]]
                           (equality (add zero 'extra) finish))
             finish
             (function/app
              (function/const* 'equality/reflexive [type-level])
              nat finish)))
          (function/lam
           [['right-previous nat]
            ['ignored
             (at-most
              'right-previous
              (add (succ 'left-previous)
                   (distance (succ 'left-previous) 'right-previous)))]]
           (let [previous-finish
                 (add 'left-previous
                      (distance 'left-previous 'right-previous))
                 finish (succ previous-finish)
                 ordered
                 (function/app 'induction-hypothesis 'right-previous)]
             (function/app
              (function/const* 'proposition/use-witness [type-level])
              nat
              (function/lam
               [['extra nat]]
               (equality (add 'right-previous 'extra) previous-finish))
              (at-most (succ 'right-previous) finish)
              ordered
              (function/lam
               [['extra nat]
                ['same
                 (equality (add 'right-previous 'extra) previous-finish)]]
               (function/app
                (function/const* 'proposition/witness [type-level])
                nat
                (function/lam
                 [['candidate-extra nat]]
                 (equality (add (succ 'right-previous) 'candidate-extra)
                           finish))
                'extra
                (congruent
                 (function/lam [['value nat]] (succ 'value))
                 (add 'right-previous 'extra) previous-finish 'same))))))
          'right)))
       'left))}))

(def distance-left-bound-spec
  {:name 'nat/distance-left-bound
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]]
    (at-most 'right (add (distance 'left 'right) 'left)))
   :value
   (function/lam
    [['left nat] ['right nat]]
    (let [middle (add 'left (distance 'left 'right))
          finish (add (distance 'left 'right) 'left)
          ordered
          (function/app (function/const* 'nat/distance-right-bound [])
                        'left 'right)]
      (function/app
       (function/const* 'proposition/use-witness [type-level])
       nat
       (function/lam [['extra nat]]
                     (equality (add 'right 'extra) middle))
       (at-most 'right finish)
       ordered
       (function/lam
        [['extra nat] ['same (equality (add 'right 'extra) middle)]]
        (function/app
         (function/const* 'proposition/witness [type-level])
         nat
         (function/lam [['candidate-extra nat]]
                       (equality (add 'right 'candidate-extra) finish))
         'extra
         (transitive
          (add 'right 'extra) middle finish 'same
          (function/app (function/const* 'nat/add-commutative [])
                        'left (distance 'left 'right))))))))})

(def definition-specs
  [heterogeneous-add-spec homogeneous-add-instance-spec nat-distance-spec])

(def theorem-specs
  [distance-successor-spec distance-commutative-spec
   distance-add-left-spec distance-add-right-spec
   distance-right-bound-spec distance-left-bound-spec])

(def constant-aliases
  {"HAdd.hAdd" 'algebra/heterogeneous-add
   "instHAdd" 'algebra/homogeneous-add-instance
   "instAddNat" 'algebra/nat-add
   "Nat.dist" 'nat/distance})

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Nat distance expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (or (:kind spec) :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :constructive-nat-distance}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Nat distance declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce add-spec checked-environment (into definition-specs theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.distance))
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
