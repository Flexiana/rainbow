(ns rainbow.math.logic.strict-contraction-uniqueness
  "Constructive uniqueness of support-relative fixed points for strict finite contractions."
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

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- recursive-max [left right]
  (function/app (function/const* 'nat/recursive-max []) left right))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- nil-list [element]
  (function/app (function/const* 'data/nil [data-level]) element))

(defn- cons-list [element head tail]
  (function/app (function/const* 'data/cons [data-level])
                element head tail))

(defn- membership [element source value]
  (function/app (function/const* 'list/membership [U])
                element source value))

(defn- map-max [element mapping source]
  (function/app (function/const* 'list/nat-map-max [U])
                element mapping source))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- source-membership [element source value]
  (function/app (function/const* 'finset-data/to-set [U])
                element source value))

(defn- finite-sup-distance [element source left right]
  (function/app (function/const* 'metric/finite-sup-distance [U])
                element source left right))

(defn- equality [level carrier left right]
  (function/equality level carrier left right))

(defn- nat-equality [left right]
  (equality type-level nat left right))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level])
                carrier value))

(defn- symmetric [level carrier left right same]
  (function/app (function/const* 'equality/symmetric [level])
                carrier left right same))

(defn- transitive [level carrier left middle right first second]
  (function/app (function/const* 'equality/transitive [level])
                carrier left middle right first second))

(defn- congruent
  [source-level target-level source target mapping left right same]
  (function/app
   (function/const* 'equality/congruent-function
                    [source-level target-level])
   source target mapping left right same))

(defn- substitute [level carrier left right same predicate at-left]
  (function/app (function/const* 'equality/substitution [level])
                carrier left right same predicate at-left))

(defn- impossible [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))

(def equal-zero-of-not-positive-spec
  (let [motive
        (function/lam
         [['value nat]]
         (function/forall
          [['not-positive
            (proposition/negation (below zero 'value))]]
          (nat-equality 'value zero)))]
    {:name 'nat/equal-zero-of-not-positive
     :universes []
     :type
     (function/forall
      [['value nat]
       ['not-positive (proposition/negation (below zero 'value))]]
      (nat-equality 'value zero))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['ignored (proposition/negation (below zero zero))]]
        (reflexive type-level nat zero))
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]
         ['not-positive
          (proposition/negation (below zero (succ 'previous)))]]
        (let [nonzero
              (function/lam
               [['same (nat-equality (succ 'previous) zero)]]
               (function/app
                (function/const* 'nat/zero-not-successor [])
                'previous
                (symmetric type-level nat
                           (succ 'previous) zero 'same)))]
          (impossible
           (nat-equality (succ 'previous) zero)
           (function/app
            'not-positive
            (function/app
             (function/const* 'nat/positive-of-nonzero [])
             (succ 'previous) nonzero)))))
       'value))}))

(def list-map-max-congruent-on-spec
  (let [pointwise
        (fn [source]
          (function/forall
           [['value 'A]
            ['member (membership 'A source 'value)]]
           (nat-equality (function/app 'left 'value)
                         (function/app 'right 'value))))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (function/forall
          [['pointwise (pointwise 'source)]]
          (nat-equality (map-max 'A 'left 'source)
                        (map-max 'A 'right 'source))))]
    {:name 'list/nat-map-max-congruent-on
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['source (list-of 'A)]
       ['pointwise (pointwise 'source)]]
      (nat-equality (map-max 'A 'left 'source)
                    (map-max 'A 'right 'source)))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['source (list-of 'A)]
       ['pointwise (pointwise 'source)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/lam
        [['ignored (pointwise (nil-list 'A))]]
        (reflexive type-level nat zero))
       (function/lam
        [['head 'A]
         ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]
         ['step-pointwise (pointwise (cons-list 'A 'head 'tail))]]
        (let [left-head (function/app 'left 'head)
              right-head (function/app 'right 'head)
              left-tail (map-max 'A 'left 'tail)
              right-tail (map-max 'A 'right 'tail)
              start (recursive-max left-head left-tail)
              middle (recursive-max right-head left-tail)
              finish (recursive-max right-head right-tail)
              head-member
              (function/app
               (function/const* 'proposition/left-disjunct [])
               (equality data-level 'A 'head 'head)
               (membership 'A 'tail 'head)
               (reflexive data-level 'A 'head))
              tail-pointwise
              (function/lam
               [['value 'A]
                ['tail-member (membership 'A 'tail 'value)]]
               (function/app
                'step-pointwise 'value
                (function/app
                 (function/const* 'proposition/right-disjunct [])
                 (equality data-level 'A 'value 'head)
                 (membership 'A 'tail 'value)
                 'tail-member)))]
          (transitive
           type-level nat start middle finish
           (congruent
            type-level type-level nat nat
            (function/lam
             [['value nat]] (recursive-max 'value left-tail))
            left-head right-head
            (function/app 'step-pointwise 'head head-member))
           (congruent
            type-level type-level nat nat
            (function/lam
             [['value nat]] (recursive-max right-head 'value))
            left-tail right-tail
            (function/app 'induction-hypothesis tail-pointwise)))))
       'source 'pointwise))}))

(def finite-sup-congruent-on-spec
  (let [pointwise
        (fn [left right]
          (function/forall
           [['state 'A]
            ['member (source-membership 'A 'source 'state)]]
           (nat-equality (function/app left 'state)
                         (function/app right 'state))))]
    {:name 'metric/finite-sup-congruent-on
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['source (exact-finset-of 'A)]
       ['left-before (function/arrow 'A nat)]
       ['right-before (function/arrow 'A nat)]
       ['left-after (function/arrow 'A nat)]
       ['right-after (function/arrow 'A nat)]
       ['left-pointwise (pointwise 'left-before 'left-after)]
       ['right-pointwise (pointwise 'right-before 'right-after)]]
      (nat-equality
       (finite-sup-distance 'A 'source 'left-before 'right-before)
       (finite-sup-distance 'A 'source 'left-after 'right-after)))
     :value
     (function/lam
      [['A type-u]
       ['source (exact-finset-of 'A)]
       ['left-before (function/arrow 'A nat)]
       ['right-before (function/arrow 'A nat)]
       ['left-after (function/arrow 'A nat)]
       ['right-after (function/arrow 'A nat)]
       ['left-pointwise (pointwise 'left-before 'left-after)]
       ['right-pointwise (pointwise 'right-before 'right-after)]]
      (function/app
       (function/const* 'list/nat-map-max-congruent-on [U])
       'A
       (function/lam
        [['state 'A]]
        (distance (function/app 'left-before 'state)
                  (function/app 'right-before 'state)))
       (function/lam
        [['state 'A]]
        (distance (function/app 'left-after 'state)
                  (function/app 'right-after 'state)))
       (enumeration 'A 'source)
       (function/lam
        [['state 'A]
         ['member
          (membership 'A (enumeration 'A 'source) 'state)]]
        (let [left-before (function/app 'left-before 'state)
              right-before (function/app 'right-before 'state)
              left-after (function/app 'left-after 'state)
              right-after (function/app 'right-after 'state)
              start (distance left-before right-before)
              middle (distance left-after right-before)
              finish (distance left-after right-after)]
          (transitive
           type-level nat start middle finish
           (congruent
            type-level type-level nat nat
            (function/lam
             [['value nat]] (distance 'value right-before))
            left-before left-after
            (function/app 'left-pointwise 'state 'member))
           (congruent
            type-level type-level nat nat
            (function/lam
             [['value nat]] (distance left-after 'value))
            right-before right-after
            (function/app 'right-pointwise 'state 'member)))))))}))

(defn- strict-contraction-context []
  (let [value-space (function/arrow 'A nat)
        sup-distance
        (fn [left right]
          (finite-sup-distance 'A 'source left right))
        transform-at
        (fn [value] (function/app 'transform value))]
    {:binders
     [['A type-u]
      ['source (exact-finset-of 'A)]
      ['transform (function/arrow value-space value-space)]
      ['left value-space]
      ['right value-space]
      ['strictly-contracts
       (function/forall
        [['candidate-left value-space]
         ['candidate-right value-space]
         ['positive
          (below zero (sup-distance 'candidate-left 'candidate-right))]]
        (below
         (sup-distance (transform-at 'candidate-left)
                       (transform-at 'candidate-right))
         (sup-distance 'candidate-left 'candidate-right)))]
      ['left-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (transform-at 'left) 'state)
         (function/app 'left 'state)))]
      ['right-fixed
       (function/forall
        [['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (nat-equality
         (function/app (transform-at 'right) 'state)
         (function/app 'right 'state)))]]
     :sup-distance sup-distance
     :transform-at transform-at}))

(def strict-contraction-fixed-points-have-zero-sup-distance-spec
  (let [{:keys [binders sup-distance transform-at]}
        (strict-contraction-context)
        original-distance (sup-distance 'left 'right)
        transformed-distance
        (sup-distance (transform-at 'left) (transform-at 'right))]
    {:name 'metric/strict-contraction-fixed-points-have-zero-sup-distance
     :universes ['u]
     :type
     (function/forall binders
                      (nat-equality original-distance zero))
     :value
     (function/lam
      binders
      (function/app
       (function/const* 'nat/equal-zero-of-not-positive [])
       original-distance
       (function/lam
        [['positive (below zero original-distance)]]
        (let [contracted
              (function/app
               'strictly-contracts 'left 'right 'positive)
              fixed-distance
              (function/app
               (function/const* 'metric/finite-sup-congruent-on [U])
               'A 'source
               (transform-at 'left) (transform-at 'right)
               'left 'right 'left-fixed 'right-fixed)
              self-below
              (substitute
               type-level nat transformed-distance original-distance
               fixed-distance
               (function/lam
                [['candidate nat]] (below 'candidate original-distance))
               contracted)]
          (function/app
           (function/const* 'nat/not-strictly-below-self [])
           original-distance self-below)))))}))

(def strict-contraction-fixed-points-unique-on-support-spec
  (let [{:keys [binders sup-distance]}
        (strict-contraction-context)]
    {:name 'metric/strict-contraction-fixed-points-unique-on-support
     :universes ['u]
     :type
     (function/forall
      binders
      (function/forall
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (nat-equality (function/app 'left 'state)
                     (function/app 'right 'state))))
     :value
     (function/lam
      binders
      (function/lam
       [['state 'A]
        ['member (source-membership 'A 'source 'state)]]
       (function/app
        (function/const* 'metric/pointwise-equal-of-finite-sup-zero [U])
        'A 'source 'left 'right
        (function/app
         (function/const*
          'metric/strict-contraction-fixed-points-have-zero-sup-distance
          [U])
         'A 'source 'transform 'left 'right
         'strictly-contracts 'left-fixed 'right-fixed)
        'state 'member)))}))

(def theorem-specs
  [equal-zero-of-not-positive-spec
   list-map-max-congruent-on-spec
   finite-sup-congruent-on-spec
   strict-contraction-fixed-points-have-zero-sup-distance-spec
   strict-contraction-fixed-points-unique-on-support-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw
       (ex-info "Strict-contraction uniqueness expression failed elaboration"
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
           :producer :constructive-strict-contraction-uniqueness}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Strict-contraction uniqueness theorem was rejected"
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
