(ns rainbow.math.finite.expectation
  "Executable finite natural mass and expectation numerators.

  This is the exact arithmetic substrate for finite probability.  Natural
  masses plus an explicit normalization scale avoid introducing floating-point
  semantics or pretending that raw fractions already form a quotient field."
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
(def one (function/app (function/const* 'data/succ []) zero))
(def successor (function/const* 'data/succ []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- add [left right]
  (function/app (function/const* 'algebra/nat-add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nat/multiply []) left right))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nat-map-sum [U])
                element mapping source))

(defn- equality [left right]
  (function/equality type-level nat left right))

(def nat-multiply-spec
  {:name 'nat/multiply
   :kind :definition
   :universes []
   :transparency :reducible
   :type (function/arrow nat nat nat)
   :value
   (function/lam
    [['left nat] ['right nat]]
    (function/app
     (function/const* 'data/Nat.rec [type-level])
     (function/lam [['ignored nat]] nat)
     zero
     (function/lam
      [['previous nat] ['previous-product nat]]
      (add 'right 'previous-product))
     'left))})

(def list-nat-map-sum-spec
  {:name 'list/nat-map-sum
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A nat)]]
    (function/arrow (list-of 'A) nat))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A nat)]
     ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] nat)
     zero
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-sum nat]]
      (add (function/app 'mapping 'head) 'tail-sum))
     'source))})

(def weight-total-spec
  {:name 'probability/weight-total
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]]
    nat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]]
    (map-sum 'A 'mass (enumeration 'A 'source)))})

(def normalized-spec
  {:name 'probability/normalized-at
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]]
    'Prop)
   :value
   (function/lam
    [['A type-u] ['scale nat] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]]
    (equality
     (function/app
      (function/const* 'probability/weight-total [U])
      'A 'source 'mass)
     'scale))})

(def expectation-numerator-spec
  {:name 'probability/expectation-numerator
   :kind :definition
   :universes ['u]
   :transparency :reducible
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]
     ['value (function/arrow 'A nat)]]
    nat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nat)]
     ['value (function/arrow 'A nat)]]
    (map-sum
     'A
     (function/lam
      [['state 'A]]
      (multiply (function/app 'value 'state)
                (function/app 'mass 'state)))
     (enumeration 'A 'source)))})

(def list-map-sum-zero-spec
  (let [zero-mapping (function/lam [['value 'A]] zero)
        motive
        (function/lam
         [['source (list-of 'A)]]
         (equality (map-sum 'A zero-mapping 'source) zero))]
    {:name 'list/nat-map-sum-zero
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (list-of 'A)]]
      (equality (map-sum 'A zero-mapping 'source) zero))
     :value
     (function/lam
      [['A type-u] ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app
        (function/const* 'equality/reflexive [type-level]) nat zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        'induction-hypothesis)
       'source))}))

(def expectation-zero-spec
  (let [source-type (exact-finset-of 'A)
        zero-value (function/lam [['state 'A]] zero)
        expectation
        (function/app
         (function/const* 'probability/expectation-numerator [U])
         'A 'source 'mass zero-value)]
    {:name 'probability/expectation-zero
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source source-type]
       ['mass (function/arrow 'A nat)]]
      (equality expectation zero))
     :value
     (function/lam
      [['A type-u] ['source source-type]
       ['mass (function/arrow 'A nat)]]
      (function/app
       (function/const* 'list/nat-map-sum-zero [U])
       'A (enumeration 'A 'source)))}))

(def one-times-spec
  {:name 'nat/one-times
   :universes []
   :type (function/forall [['value nat]] (equality (multiply one 'value) 'value))
   :value
   (function/lam
    [['value nat]]
    (function/app
     (function/const* 'algebra/nat-add-zero-right []) 'value))})

(def times-zero-spec
  (let [motive
        (function/lam
         [['value nat]]
         (equality (multiply 'value zero) zero))]
    {:name 'nat/times-zero
     :universes []
     :type
     (function/forall [['value nat]] (equality (multiply 'value zero) zero))
     :value
     (function/lam
      [['value nat]]
      (function/app
       (function/const* 'data/Nat.rec [zero-level])
       motive
       (function/app
        (function/const* 'equality/reflexive [type-level]) nat zero)
       (function/lam
        [['previous nat]
         ['induction-hypothesis (function/app motive 'previous)]]
        'induction-hypothesis)
       'value))}))

(def definition-specs
  [nat-multiply-spec list-nat-map-sum-spec weight-total-spec
   normalized-spec expectation-numerator-spec])

(def theorem-specs
  [list-map-sum-zero-spec expectation-zero-spec one-times-spec times-zero-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite expectation expression failed elaboration"
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
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (or (:transparency spec) :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-expectation-foundation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite expectation declaration was rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-environment [checked-environment]
  (reduce add-spec checked-environment
          (into definition-specs theorem-specs)))

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
