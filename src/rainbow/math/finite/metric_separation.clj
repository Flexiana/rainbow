(ns rainbow.math.finite.metric-separation
  "Constructive zero and positivity separation for finite natural sup-distance."
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

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- at-most [left right]
  (function/app (function/const* 'nat/at-most []) left right))

(defn- below [left right]
  (function/app (function/const* 'nat/strict-below []) left right))

(defn- distance [left right]
  (function/app (function/const* 'nat/distance []) left right))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

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

(defn- unequal [level carrier left right]
  (proposition/negation (equality level carrier left right)))

(defn- reflexive [level carrier value]
  (function/app (function/const* 'equality/reflexive [level])
                carrier value))

(defn- symmetric [level carrier left right same]
  (function/app (function/const* 'equality/symmetric [level])
                carrier left right same))

(defn- impossible [result contradiction]
  (function/app (function/const* 'proposition/explode [])
                result contradiction))

(def equal-zero-of-at-most-zero-spec
  (let [motive
        (function/lam
         [['value nat]]
         (function/forall
          [['ordered (at-most 'value zero)]]
          (nat-equality 'value zero)))]
    {:name 'nat/equal-zero-of-at-most-zero
     :universes []
     :type
     (function/forall
      [['value nat] ['ordered (at-most 'value zero)]]
      (nat-equality 'value zero))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/lam
        [['ordered (at-most zero zero)]]
        (reflexive type-level nat zero))
       (function/lam
        [['previous nat]
         ['ignored (function/app motive 'previous)]
         ['ordered (at-most (succ 'previous) zero)]]
        (function/app
         (function/const* 'proposition/use-witness [type-level])
         nat
         (function/lam
          [['extra nat]]
          (nat-equality (add (succ 'previous) 'extra) zero))
         (nat-equality (succ 'previous) zero)
         'ordered
         (function/lam
          [['extra nat]
           ['successor-is-zero
            (nat-equality (add (succ 'previous) 'extra) zero)]]
          (impossible
           (nat-equality (succ 'previous) zero)
           (function/app
            (function/const* 'nat/zero-not-successor [])
            (add 'previous 'extra)
            (symmetric type-level nat
                       (succ (add 'previous 'extra)) zero
                       'successor-is-zero))))))
       'value))}))

(def list-map-max-zero-of-memberwise-zero-spec
  {:name 'list/nat-map-max-zero-of-memberwise-zero
   :universes ['u]
   :type
   (function/forall
    [['A type-u]
     ['mapping (function/arrow 'A nat)]
     ['source (list-of 'A)]
     ['memberwise-zero
      (function/forall
       [['value 'A]
        ['member (membership 'A 'source 'value)]]
       (nat-equality (function/app 'mapping 'value) zero))]]
    (nat-equality (map-max 'A 'mapping 'source) zero))
   :value
   (function/lam
    [['A type-u]
     ['mapping (function/arrow 'A nat)]
     ['source (list-of 'A)]
     ['memberwise-zero
      (function/forall
       [['value 'A]
        ['member (membership 'A 'source 'value)]]
       (nat-equality (function/app 'mapping 'value) zero))]]
    (let [maximum (map-max 'A 'mapping 'source)
          bounded
          (function/app
           (function/const* 'list/nat-map-max-bounded [U])
           'A 'mapping zero 'source
           (function/lam
            [['value 'A]
             ['member (membership 'A 'source 'value)]]
            (function/app
             (function/const* 'nat/at-most-rewrite-left [])
             (function/app 'mapping 'value) zero zero
             (function/app 'memberwise-zero 'value 'member)
             (function/app
              (function/const* 'nat/at-most-reflexive []) zero))))]
      (function/app
       (function/const* 'nat/equal-zero-of-at-most-zero [])
       maximum bounded)))})

(def finite-sup-zero-of-pointwise-equal-spec
  (let [pointwise-equal
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (nat-equality (function/app 'left 'state)
                       (function/app 'right 'state)))]
    {:name 'metric/finite-sup-zero-of-pointwise-equal
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['pointwise-equal pointwise-equal]]
      (nat-equality
       (finite-sup-distance 'A 'source 'left 'right) zero))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]
       ['pointwise-equal pointwise-equal]]
      (function/app
       (function/const* 'list/nat-map-max-zero-of-memberwise-zero [U])
       'A
       (function/lam
        [['state 'A]]
        (distance (function/app 'left 'state)
                  (function/app 'right 'state)))
       (enumeration 'A 'source)
       (function/lam
        [['state 'A]
         ['member (membership 'A (enumeration 'A 'source) 'state)]]
        (function/app
         (function/const* 'nat/distance-zero-of-equal [])
         (function/app 'left 'state) (function/app 'right 'state)
         (function/app 'pointwise-equal 'state 'member)))))}))

(def pointwise-equal-of-finite-sup-zero-spec
  {:name 'metric/pointwise-equal-of-finite-sup-zero
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]
     ['sup-is-zero
      (nat-equality
       (finite-sup-distance 'A 'source 'left 'right) zero)]
     ['state 'A]
     ['member (source-membership 'A 'source 'state)]]
    (nat-equality (function/app 'left 'state)
                  (function/app 'right 'state)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]
     ['sup-is-zero
      (nat-equality
       (finite-sup-distance 'A 'source 'left 'right) zero)]
     ['state 'A]
     ['member (source-membership 'A 'source 'state)]]
    (let [point-distance
          (distance (function/app 'left 'state)
                    (function/app 'right 'state))
          supremum (finite-sup-distance 'A 'source 'left 'right)
          bounded
          (function/app
           (function/const* 'metric/finite-sup-upper-bound [U])
           'A 'source 'left 'right 'state 'member)
          bounded-by-zero
          (function/app
           (function/const* 'nat/at-most-rewrite-right [])
           point-distance supremum zero 'sup-is-zero bounded)
          point-is-zero
          (function/app
           (function/const* 'nat/equal-zero-of-at-most-zero [])
           point-distance bounded-by-zero)]
      (function/app
       (function/const* 'nat/equal-of-distance-zero [])
       (function/app 'left 'state) (function/app 'right 'state)
       point-is-zero)))})

(def finite-sup-zero-equivalent-pointwise-equal-spec
  (let [sup-is-zero
        (nat-equality
         (finite-sup-distance 'A 'source 'left 'right) zero)
        pointwise-equal
        (function/forall
         [['state 'A]
          ['member (source-membership 'A 'source 'state)]]
         (nat-equality (function/app 'left 'state)
                       (function/app 'right 'state)))]
    {:name 'metric/finite-sup-zero-equivalent-pointwise-equal
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (proposition/equivalence sup-is-zero pointwise-equal))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['left (function/arrow 'A nat)]
       ['right (function/arrow 'A nat)]]
      (function/app
       (function/const* 'proposition/equivalence-intro [])
       sup-is-zero pointwise-equal
       (function/lam
        [['same sup-is-zero]
         ['state 'A]
         ['member (source-membership 'A 'source 'state)]]
        (function/app
         (function/const* 'metric/pointwise-equal-of-finite-sup-zero [U])
         'A 'source 'left 'right 'same 'state 'member))
       (function/lam
        [['same pointwise-equal]]
        (function/app
         (function/const* 'metric/finite-sup-zero-of-pointwise-equal [U])
         'A 'source 'left 'right 'same))))}))

(def finite-sup-positive-of-pointwise-not-equal-spec
  {:name 'metric/finite-sup-positive-of-pointwise-not-equal
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]
     ['state 'A]
     ['member (source-membership 'A 'source 'state)]
     ['different
      (unequal type-level nat
               (function/app 'left 'state)
               (function/app 'right 'state))]]
    (below zero (finite-sup-distance 'A 'source 'left 'right)))
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['left (function/arrow 'A nat)]
     ['right (function/arrow 'A nat)]
     ['state 'A]
     ['member (source-membership 'A 'source 'state)]
     ['different
      (unequal type-level nat
               (function/app 'left 'state)
               (function/app 'right 'state))]]
    (let [supremum (finite-sup-distance 'A 'source 'left 'right)
          nonzero
          (function/lam
           [['sup-is-zero (nat-equality supremum zero)]]
           (function/app
            'different
            (function/app
             (function/const* 'metric/pointwise-equal-of-finite-sup-zero [U])
             'A 'source 'left 'right 'sup-is-zero 'state 'member)))]
      (function/app
       (function/const* 'nat/positive-of-nonzero [])
       supremum nonzero)))})

(def theorem-specs
  [equal-zero-of-at-most-zero-spec
   list-map-max-zero-of-memberwise-zero-spec
   finite-sup-zero-of-pointwise-equal-spec
   pointwise-equal-of-finite-sup-zero-spec
   finite-sup-zero-equivalent-pointwise-equal-spec
   finite-sup-positive-of-pointwise-not-equal-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite metric-separation expression failed elaboration"
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
           :producer :constructive-finite-metric-separation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite metric-separation theorem was rejected"
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
