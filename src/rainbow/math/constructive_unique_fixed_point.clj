(ns rainbow.math.constructive-unique-fixed-point
  "Constructive existence and support-relative uniqueness for strict Nat contractions."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nat (function/const* 'data/Nat []))
(def zero (function/const* 'data/zero []))
(def successor (function/const* 'data/succ []))

(defn- succ [value]
  (function/app successor value))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- finite-sup-distance [element source left right]
  (function/app (function/const* 'metric/finite-sup-distance [U])
                element source left right))

(defn- nat-iterate [carrier transform steps initial]
  (function/app (function/const* 'function/nat-iterate [U])
                carrier transform steps initial))

(defn- context []
  (let [value-space (function/arrow 'A nat)
        iterate (fn [steps]
                  (nat-iterate value-space 'transform steps 'initial))
        distance
        (fn [left right]
          (finite-sup-distance 'A 'source left right))
        initial-distance (distance 'initial (function/app 'transform 'initial))
        fixed
        (fn [value]
          (function/forall
           [['state 'A]
            ['member (source-membership 'A 'source 'state)]]
           (nat-equality
            (function/app 'transform value 'state)
            (function/app value 'state))))
        agrees
        (fn [left right]
          (function/forall
           [['state 'A]
            ['member (source-membership 'A 'source 'state)]]
           (nat-equality (function/app left 'state)
                         (function/app right 'state))))]
    {:value-space value-space :iterate iterate :distance distance
     :initial-distance initial-distance :fixed fixed :agrees agrees
     :binders
     [['A type-u]
      ['source (exact-finset-of 'A)]
      ['transform (function/arrow value-space value-space)]
      ['initial value-space]
      ['strictly-contracts
       (function/forall
        [['left value-space] ['right value-space]
         ['positive (below zero (distance 'left 'right))]]
        (below (distance (function/app 'transform 'left)
                         (function/app 'transform 'right))
               (distance 'left 'right)))]]}))

(def bounded-fixed-point-agrees-spec
  (let [{:keys [binders value-space iterate initial-distance fixed agrees]}
        (context)]
    {:name 'metric/strict-contraction-bounded-fixed-point-agrees-with-fixed-point
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['steps nat]
        ['bounded (at-most 'steps initial-distance)]
        ['iterate-fixed (fixed (iterate 'steps))]
        ['candidate value-space]
        ['candidate-fixed (fixed 'candidate)]]
       (agrees (iterate 'steps) 'candidate)))
     :value
     (function/lam
      binders
      (function/lam
       [['steps nat]
        ['ignored-bounded (at-most 'steps initial-distance)]
        ['iterate-fixed (fixed (iterate 'steps))]
        ['candidate value-space]
        ['candidate-fixed (fixed 'candidate)]]
       (function/app
        (function/const*
         'metric/strict-contraction-fixed-points-unique-on-support [U])
        'A 'source 'transform (iterate 'steps) 'candidate
        'strictly-contracts 'iterate-fixed 'candidate-fixed)))}))

(defn- canonical-predicate
  [value-space iterate initial-distance fixed agrees]
  (function/lam
   [['steps nat]]
   (proposition/conjunction
    (at-most 'steps initial-distance)
    (proposition/conjunction
     (fixed (iterate 'steps))
     (function/forall
      [['candidate value-space]
       ['candidate-fixed (fixed 'candidate)]]
      (agrees (iterate 'steps) 'candidate))))))

(def bounded-canonical-fixed-point-spec
  (let [{:keys [binders value-space iterate initial-distance fixed agrees]}
        (context)
        bounded-fixed-predicate
        (function/lam
         [['steps nat]]
         (proposition/conjunction
          (at-most 'steps initial-distance)
          (fixed (iterate 'steps))))
        target-predicate
        (canonical-predicate value-space iterate initial-distance fixed agrees)]
    {:name 'metric/strict-contraction-has-bounded-canonical-support-fixed-point
     :universes ['u]
     :type
     (function/forall
      binders
      (proposition/existence type-level nat target-predicate))
     :value
     (function/lam
      binders
      (let [exists-bounded-fixed
            (function/app
             (function/const*
              'metric/strict-contraction-has-bounded-support-fixed-point [U])
             'A 'source 'transform 'initial 'strictly-contracts)]
        (function/app
         (function/const* 'proposition/use-witness [type-level])
         nat bounded-fixed-predicate
         (proposition/existence type-level nat target-predicate)
         exists-bounded-fixed
         (function/lam
          [['steps nat]
           ['evidence (function/app bounded-fixed-predicate 'steps)]]
          (let [bounded
                (function/app
                 (function/const* 'proposition/left [])
                 (at-most 'steps initial-distance)
                 (fixed (iterate 'steps)) 'evidence)
                iterate-fixed
                (function/app
                 (function/const* 'proposition/right [])
                 (at-most 'steps initial-distance)
                 (fixed (iterate 'steps)) 'evidence)
                canonical
                (function/lam
                 [['candidate value-space]
                  ['candidate-fixed (fixed 'candidate)]]
                 (function/app
                  (function/const*
                   'metric/strict-contraction-bounded-fixed-point-agrees-with-fixed-point
                   [U])
                  'A 'source 'transform 'initial 'strictly-contracts
                  'steps bounded iterate-fixed 'candidate 'candidate-fixed))]
            (function/app
             (function/const* 'proposition/witness [type-level])
             nat target-predicate 'steps
             (function/app
              (function/const* 'proposition/conjoin [])
              (at-most 'steps initial-distance)
              (proposition/conjunction
               (fixed (iterate 'steps))
               (function/forall
                [['candidate value-space]
                 ['candidate-fixed (fixed 'candidate)]]
                (agrees (iterate 'steps) 'candidate)))
              bounded
              (function/app
               (function/const* 'proposition/conjoin [])
               (fixed (iterate 'steps))
               (function/forall
                [['candidate value-space]
                 ['candidate-fixed (fixed 'candidate)]]
                (agrees (iterate 'steps) 'candidate))
               iterate-fixed canonical))))))))}))

(def exists-and-unique-spec
  (let [{:keys [binders value-space iterate initial-distance fixed agrees]}
        (context)
        canonical
        (canonical-predicate value-space iterate initial-distance fixed agrees)
        exists-fixed
        (proposition/existence
         data-level value-space (function/lam [['value value-space]] (fixed 'value)))
        unique-on-support
        (function/forall
         [['left value-space] ['right value-space]
          ['left-fixed (fixed 'left)] ['right-fixed (fixed 'right)]]
         (agrees 'left 'right))]
    {:name 'metric/strict-contraction-support-fixed-point-exists-and-is-unique
     :universes ['u]
     :type
     (function/forall binders
                      (proposition/conjunction exists-fixed unique-on-support))
     :value
     (function/lam
      binders
      (let [canonical-exists
            (function/app
             (function/const*
              'metric/strict-contraction-has-bounded-canonical-support-fixed-point
              [U])
             'A 'source 'transform 'initial 'strictly-contracts)
            fixed-exists
            (function/app
             (function/const* 'proposition/use-witness [type-level])
             nat canonical exists-fixed canonical-exists
             (function/lam
              [['steps nat]
               ['evidence (function/app canonical 'steps)]]
              (let [rest
                    (function/app
                     (function/const* 'proposition/right [])
                     (at-most 'steps initial-distance)
                     (proposition/conjunction
                      (fixed (iterate 'steps))
                      (function/forall
                       [['candidate value-space]
                        ['candidate-fixed (fixed 'candidate)]]
                       (agrees (iterate 'steps) 'candidate)))
                     'evidence)
                    iterate-fixed
                    (function/app
                     (function/const* 'proposition/left [])
                     (fixed (iterate 'steps))
                     (function/forall
                      [['candidate value-space]
                       ['candidate-fixed (fixed 'candidate)]]
                      (agrees (iterate 'steps) 'candidate))
                     rest)]
                (function/app
                 (function/const* 'proposition/witness [data-level])
                 value-space
                 (function/lam [['value value-space]] (fixed 'value))
                 (iterate 'steps) iterate-fixed))))
            unique-proof
            (function/lam
             [['left value-space] ['right value-space]
              ['left-fixed (fixed 'left)] ['right-fixed (fixed 'right)]]
             (function/app
              (function/const*
               'metric/strict-contraction-fixed-points-unique-on-support [U])
              'A 'source 'transform 'left 'right
              'strictly-contracts 'left-fixed 'right-fixed))]
        (function/app
         (function/const* 'proposition/conjoin [])
         exists-fixed unique-on-support fixed-exists unique-proof)))}))

(def theorem-specs
  [bounded-fixed-point-agrees-spec
   bounded-canonical-fixed-point-spec
   exists-and-unique-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Constructive unique fixed-point expression failed elaboration"
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
          {:origin :native :producer :constructive-unique-fixed-point}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Constructive unique fixed-point declaration rejected"
                {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
