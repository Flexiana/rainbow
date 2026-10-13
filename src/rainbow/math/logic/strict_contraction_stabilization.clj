(ns rainbow.math.logic.strict-contraction-stabilization
  "Constructive bounded stabilization of strict contractions in a finite Nat sup metric."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
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

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- nat-equality [left right]
  (function/equality type-level nat left right))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level])
                carrier value))

(defn- symmetric [level carrier left right same]
  (function/app (function/const* 'equality/symmetric [level])
                carrier left right same))

(defn- congruent
  [source-level target-level source target mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [source-level target-level])
   source target mapping left right same))

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

(def at-most-successor-cancel-spec
  {:name 'nat/at-most-successor-cancel
   :universes []
   :type
   (function/forall
    [['left nat] ['right nat]
     ['ordered (at-most (succ 'left) (succ 'right))]]
    (at-most 'left 'right))
   :value
   (function/lam
    [['left nat] ['right nat]
     ['ordered (at-most (succ 'left) (succ 'right))]]
    (function/app
     (function/const* 'proposition/use-witness [type-level])
     nat
     (function/lam
      [['extra nat]]
      (nat-equality (add (succ 'left) 'extra) (succ 'right)))
     (at-most 'left 'right) 'ordered
     (function/lam
      [['extra nat]
       ['same (nat-equality (add (succ 'left) 'extra) (succ 'right))]]
      (function/app
       (function/const* 'proposition/witness [type-level])
       nat
       (function/lam
        [['gap nat]] (nat-equality (add 'left 'gap) 'right))
       'extra
       (function/app
        (function/const* 'nat/successor-injective [])
        (add 'left 'extra) 'right 'same)))))} )

(def strict-below-at-most-successor-bound-spec
  {:name 'nat/strict-below-of-strict-below-at-most-successor
   :universes []
   :type
   (function/forall
    [['left nat] ['middle nat] ['bound nat]
     ['strict (below 'left 'middle)]
     ['bounded (at-most 'middle (succ 'bound))]]
    (at-most 'left 'bound))
   :value
   (function/lam
    [['left nat] ['middle nat] ['bound nat]
     ['strict (below 'left 'middle)]
     ['bounded (at-most 'middle (succ 'bound))]]
    (function/app
     (function/const* 'nat/at-most-successor-cancel [])
     'left 'bound
     (function/app
      (function/const* 'nat/at-most-transitive [])
      (succ 'left) 'middle (succ 'bound) 'strict 'bounded)))} )

(def nat-iterate-spec
  {:name 'function/nat-iterate
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['C type-u] ['transform (function/arrow 'C 'C)]]
    (function/arrow nat 'C 'C))
   :value
   (function/lam
    [['C type-u] ['transform (function/arrow 'C 'C)]
     ['steps nat] ['initial 'C]]
    (function/app
     (function/const* 'data/Nat.rec [data-level])
     (function/lam [['ignored nat]] 'C)
     'initial
     (function/lam
      [['ignored-step nat] ['previous 'C]]
      (function/app 'transform 'previous))
     'steps))})

(def nat-iterate-zero-spec
  {:name 'function/nat-iterate-zero
   :universes ['u]
   :type
   (function/forall
    [['C type-u] ['transform (function/arrow 'C 'C)] ['initial 'C]]
    (function/equality data-level 'C
                       (nat-iterate 'C 'transform zero 'initial)
                       'initial))
   :value
   (function/lam
    [['C type-u] ['transform (function/arrow 'C 'C)] ['initial 'C]]
    (reflexive data-level 'C 'initial))})

(def nat-iterate-successor-spec
  {:name 'function/nat-iterate-successor
   :universes ['u]
   :type
   (function/forall
    [['C type-u] ['transform (function/arrow 'C 'C)]
     ['steps nat] ['initial 'C]]
    (function/equality
     data-level 'C
     (nat-iterate 'C 'transform (succ 'steps) 'initial)
     (function/app 'transform
                   (nat-iterate 'C 'transform 'steps 'initial))))
   :value
   (function/lam
    [['C type-u] ['transform (function/arrow 'C 'C)]
     ['steps nat] ['initial 'C]]
    (reflexive data-level 'C
               (function/app 'transform
                             (nat-iterate 'C 'transform 'steps 'initial))))})

(defn- descent-witness [sequence bound]
  (function/lam
   [['steps nat]]
   (proposition/conjunction
    (at-most 'steps bound)
    (nat-equality (function/app sequence 'steps) zero))))

(defn- strictly-descending [sequence]
  (function/forall
   [['steps nat]
    ['positive (below zero (function/app sequence 'steps))]]
   (below (function/app sequence (succ 'steps))
          (function/app sequence 'steps))))

(def equal-zero-or-positive-spec
  (let [motive
        (function/lam
         [['value nat]]
         (proposition/disjunction
          (nat-equality 'value zero)
          (below zero 'value)))]
    {:name 'nat/equal-zero-or-positive
     :universes []
     :type
     (function/forall
      [['value nat]]
      (proposition/disjunction
       (nat-equality 'value zero)
       (below zero 'value)))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/app
        (function/const* 'proposition/left-disjunct [])
        (nat-equality zero zero) (below zero zero)
        (reflexive type-level nat zero))
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]]
        (function/app
         (function/const* 'proposition/right-disjunct [])
         (nat-equality (succ 'previous) zero)
         (below zero (succ 'previous))
         (function/app
          (function/const* 'proposition/witness [type-level])
          nat
          (function/lam
           [['gap nat]]
           (nat-equality (add (succ zero) 'gap) (succ 'previous)))
          'previous
          (reflexive type-level nat (succ 'previous)))))
       'value))}))

(def descending-sequence-reaches-zero-spec
  (let [claim
        (fn [bound sequence]
          (proposition/existence
           type-level nat (descent-witness sequence bound)))
        motive
        (function/lam
         [['bound nat]]
         (function/forall
          [['sequence (function/arrow nat nat)]
           ['initial-bounded
            (at-most (function/app 'sequence zero) 'bound)]
           ['descending (strictly-descending 'sequence)]]
          (claim 'bound 'sequence)))]
    {:name 'nat/strictly-descending-sequence-reaches-zero-within-bound
     :universes []
     :type
     (function/forall
      [['bound nat] ['sequence (function/arrow nat nat)]
       ['initial-bounded
        (at-most (function/app 'sequence zero) 'bound)]
       ['descending (strictly-descending 'sequence)]]
      (claim 'bound 'sequence))
     :value
     (function/lam
      [['bound nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['sequence (function/arrow nat nat)]
         ['initial-bounded
          (at-most (function/app 'sequence zero) zero)]
         ['ignored (strictly-descending 'sequence)]]
        (let [at-zero
              (function/app
               (function/const* 'nat/equal-zero-of-at-most-zero [])
               (function/app 'sequence zero) 'initial-bounded)]
          (function/app
           (function/const* 'proposition/witness [type-level])
           nat (descent-witness 'sequence zero) zero
           (function/app
            (function/const* 'proposition/conjoin [])
            (at-most zero zero)
            (nat-equality (function/app 'sequence zero) zero)
            (function/app (function/const* 'nat/at-most-reflexive []) zero)
            at-zero))))
       (function/lam
        [['previous-bound nat]
         ['induction-hypothesis (function/app motive 'previous-bound)]
         ['sequence (function/arrow nat nat)]
         ['initial-bounded
          (at-most (function/app 'sequence zero) (succ 'previous-bound))]
         ['descending (strictly-descending 'sequence)]]
        (let [current (function/app 'sequence zero)
              successor-bound (succ 'previous-bound)
              result (claim successor-bound 'sequence)
              zero-case (nat-equality current zero)
              positive-case (below zero current)
              dichotomy
              (function/app
               (function/const* 'nat/equal-zero-or-positive []) current)]
          (function/app
           (function/const* 'proposition/use-disjunction [])
           zero-case positive-case result dichotomy
           (function/lam
            [['at-zero zero-case]]
            (function/app
             (function/const* 'proposition/witness [type-level])
             nat (descent-witness 'sequence successor-bound) zero
             (function/app
              (function/const* 'proposition/conjoin [])
              (at-most zero successor-bound) zero-case
              (function/app
               (function/const* 'nat/at-most-transitive [])
               zero current successor-bound
               (function/app
                (function/const* 'proposition/witness [type-level])
                nat
                (function/lam
                 [['gap nat]] (nat-equality (add zero 'gap) current))
                current (reflexive type-level nat current))
               'initial-bounded)
              'at-zero)))
           (function/lam
            [['positive positive-case]]
            (let [shifted
                  (function/lam
                   [['steps nat]]
                   (function/app 'sequence (succ 'steps)))
                  next-bounded
                  (function/app
                   (function/const*
                    'nat/strict-below-of-strict-below-at-most-successor [])
                   (function/app 'sequence (succ zero))
                   current 'previous-bound
                   (function/app 'descending zero 'positive)
                   'initial-bounded)
                  shifted-descending
                  (function/lam
                   [['steps nat]
                    ['at-positive
                     (below zero (function/app shifted 'steps))]]
                   (function/app 'descending (succ 'steps) 'at-positive))
                  reached
                  (function/app 'induction-hypothesis
                                shifted next-bounded shifted-descending)
                  previous-predicate
                  (descent-witness shifted 'previous-bound)
                  target-predicate
                  (descent-witness 'sequence successor-bound)]
              (function/app
               (function/const* 'proposition/use-witness [type-level])
               nat previous-predicate result reached
               (function/lam
                [['steps nat]
                 ['evidence (function/app previous-predicate 'steps)]]
                (let [bounded
                      (function/app
                       (function/const* 'proposition/left [])
                       (at-most 'steps 'previous-bound)
                       (nat-equality (function/app shifted 'steps) zero)
                       'evidence)
                      zero-at-successor
                      (function/app
                       (function/const* 'proposition/right [])
                       (at-most 'steps 'previous-bound)
                       (nat-equality (function/app shifted 'steps) zero)
                       'evidence)
                      successor-bounded
                      (function/app
                       (function/const* 'proposition/use-witness [type-level])
                       nat
                       (function/lam
                        [['gap nat]]
                        (nat-equality (add 'steps 'gap) 'previous-bound))
                       (at-most (succ 'steps) successor-bound)
                       bounded
                       (function/lam
                        [['gap nat]
                         ['same
                          (nat-equality (add 'steps 'gap)
                                        'previous-bound)]]
                        (function/app
                         (function/const* 'proposition/witness [type-level])
                         nat
                         (function/lam
                          [['successor-gap nat]]
                          (nat-equality
                           (add (succ 'steps) 'successor-gap)
                           successor-bound))
                         'gap
                         (congruent
                          type-level type-level nat nat
                          (function/lam [['value nat]] (succ 'value))
                          (add 'steps 'gap) 'previous-bound 'same))))]
                  (function/app
                   (function/const* 'proposition/witness [type-level])
                   nat target-predicate (succ 'steps)
                   (function/app
                    (function/const* 'proposition/conjoin [])
                    (at-most (succ 'steps) successor-bound)
                    (nat-equality
                     (function/app 'sequence (succ 'steps)) zero)
                    successor-bounded zero-at-successor))))))))))
       'bound))}))

(defn- contraction-context []
  (let [value-space (function/arrow 'A nat)
        iterate (fn [steps]
                  (nat-iterate value-space 'transform steps 'initial))
        distance-at
        (fn [left right]
          (finite-sup-distance 'A 'source left right))
        consecutive
        (fn [steps]
          (distance-at (iterate steps) (iterate (succ steps))))]
    {:value-space value-space
     :iterate iterate
     :distance-at distance-at
     :consecutive consecutive
     :binders
     [['A type-u]
      ['source (exact-finset-of 'A)]
      ['transform (function/arrow value-space value-space)]
      ['initial value-space]
      ['strictly-contracts
       (function/forall
        [['left value-space] ['right value-space]
         ['positive (below zero (distance-at 'left 'right))]]
        (below (distance-at (function/app 'transform 'left)
                            (function/app 'transform 'right))
               (distance-at 'left 'right)))]]}))

(def consecutive-distance-decreases-spec
  (let [{:keys [binders iterate consecutive]} (contraction-context)]
    {:name 'metric/strict-contraction-consecutive-iterate-distance-decreases
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['steps nat]
        ['positive (below zero (consecutive 'steps))]]
       (below (consecutive (succ 'steps))
              (consecutive 'steps))))
     :value
     (function/lam
      binders
      (function/lam
       [['steps nat]
        ['positive (below zero (consecutive 'steps))]]
       (function/app 'strictly-contracts
                     (iterate 'steps) (iterate (succ 'steps))
                     'positive)))}))

(def iterate-stabilizes-spec
  (let [{:keys [binders consecutive]} (contraction-context)
        initial-distance (consecutive zero)
        sequence (function/lam [['steps nat]] (consecutive 'steps))]
    {:name 'metric/strict-contraction-iterate-stabilizes-within-initial-distance
     :universes ['u]
     :type
     (function/forall
      binders
      (proposition/existence
       type-level nat (descent-witness sequence initial-distance)))
     :value
     (function/lam
      binders
      (function/app
       (function/const*
        'nat/strictly-descending-sequence-reaches-zero-within-bound [])
       initial-distance sequence
       (function/app (function/const* 'nat/at-most-reflexive [])
                     initial-distance)
       (function/lam
        [['steps nat]
         ['positive (below zero (consecutive 'steps))]]
        (function/app
         (function/const*
          'metric/strict-contraction-consecutive-iterate-distance-decreases
          [U])
         'A 'source 'transform 'initial 'strictly-contracts
         'steps 'positive))))}))

(def bounded-support-fixed-point-spec
  (let [{:keys [binders iterate consecutive]} (contraction-context)
        initial-distance (consecutive zero)
        sequence (function/lam [['steps nat]] (consecutive 'steps))
        stabilization-predicate (descent-witness sequence initial-distance)
        fixed-predicate
        (function/lam
         [['steps nat]]
         (proposition/conjunction
          (at-most 'steps initial-distance)
          (function/forall
           [['state 'A]
            ['member (source-membership 'A 'source 'state)]]
           (nat-equality
            (function/app 'transform (iterate 'steps) 'state)
            (function/app (iterate 'steps) 'state)))))]
    {:name 'metric/strict-contraction-has-bounded-support-fixed-point
     :universes ['u]
     :type
     (function/forall
      binders
      (proposition/existence type-level nat fixed-predicate))
     :value
     (function/lam
      binders
      (let [stabilizes
            (function/app
             (function/const*
              'metric/strict-contraction-iterate-stabilizes-within-initial-distance
              [U])
             'A 'source 'transform 'initial 'strictly-contracts)]
        (function/app
         (function/const* 'proposition/use-witness [type-level])
         nat stabilization-predicate
         (proposition/existence type-level nat fixed-predicate)
         stabilizes
         (function/lam
          [['steps nat]
           ['evidence (function/app stabilization-predicate 'steps)]]
          (let [bounded
                (function/app
                 (function/const* 'proposition/left [])
                 (at-most 'steps initial-distance)
                 (nat-equality (function/app sequence 'steps) zero)
                 'evidence)
                zero-distance
                (function/app
                 (function/const* 'proposition/right [])
                 (at-most 'steps initial-distance)
                 (nat-equality (function/app sequence 'steps) zero)
                 'evidence)
                fixed-on-support
                (function/lam
                 [['state 'A]
                  ['member (source-membership 'A 'source 'state)]]
                 (symmetric
                  type-level nat
                  (function/app (iterate 'steps) 'state)
                  (function/app 'transform (iterate 'steps) 'state)
                  (function/app
                   (function/const*
                    'metric/pointwise-equal-of-finite-sup-zero [U])
                   'A 'source
                   (iterate 'steps) (iterate (succ 'steps))
                   zero-distance 'state 'member)))]
            (function/app
             (function/const* 'proposition/witness [type-level])
             nat fixed-predicate 'steps
             (function/app
              (function/const* 'proposition/conjoin [])
              (at-most 'steps initial-distance)
              (function/forall
               [['state 'A]
                ['member (source-membership 'A 'source 'state)]]
               (nat-equality
                (function/app 'transform (iterate 'steps) 'state)
                (function/app (iterate 'steps) 'state)))
              bounded fixed-on-support)))))))}))

(def definition-specs [nat-iterate-spec])

(def theorem-specs
  [at-most-successor-cancel-spec
   strict-below-at-most-successor-bound-spec
   equal-zero-or-positive-spec
   nat-iterate-zero-spec
   nat-iterate-successor-spec
   descending-sequence-reaches-zero-spec
   consecutive-distance-decreases-spec
   iterate-stabilizes-spec
   bounded-support-fixed-point-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Strict-contraction stabilization expression failed elaboration"
                {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        kind (or (:kind spec) :theorem)
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind kind
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :strict-contraction-stabilization}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw
       (ex-info "Strict-contraction stabilization declaration rejected"
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
  (module/install-module checked-environment 'rainbow.math.logic.strict-contraction-stabilization))
(defn theorem-ids [checked-environment]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        theorem-specs))
