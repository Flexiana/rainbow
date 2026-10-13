(ns rainbow.math.finite.rational-expectation
  "Finite nonnegative-rational folds and expectations with congruence proofs."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.term :as term]))

(def zero-level [:zero])
(def type-level [:succ zero-level])
(def U [:param 'u])
(def data-level [:succ U])
(def type-u [:sort data-level])
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def nnrat-zero (function/const* 'nnrat/zero []))

(defn- list-of [element]
  (function/app (function/const* 'data/List [data-level]) element))

(defn- exact-finset-of [element]
  (function/app (function/const* 'finset-data/Finset [U]) element))

(defn- enumeration [element source]
  (function/app (function/const* 'finset-data/enumeration [U])
                element source))

(defn- add [left right]
  (function/app (function/const* 'nnrat/add []) left right))

(defn- multiply [left right]
  (function/app (function/const* 'nnrat/multiply []) left right))

(defn- equivalent [left right]
  (function/app (function/const* 'nnrat/equivalent []) left right))

(defn- map-sum [element mapping source]
  (function/app (function/const* 'list/nnrat-map-sum [U])
                element mapping source))

(defn- expectation [element source mass value]
  (function/app
   (function/const* 'probability/nnrat-expectation [U])
   element source mass value))

(def list-map-sum-spec
  {:name 'list/nnrat-map-sum
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['mapping (function/arrow 'A nnrat)]]
    (function/arrow (list-of 'A) nnrat))
   :value
   (function/lam
    [['A type-u] ['mapping (function/arrow 'A nnrat)]
     ['source (list-of 'A)]]
    (function/app
     (function/const* 'data/List.rec [data-level type-level])
     'A
     (function/lam [['ignored (list-of 'A)]] nnrat)
     nnrat-zero
     (function/lam
      [['head 'A] ['tail (list-of 'A)] ['tail-sum nnrat]]
      (add (function/app 'mapping 'head) 'tail-sum))
     'source))})

(def expectation-spec
  {:name 'probability/nnrat-expectation
   :kind :definition
   :universes ['u]
   :type
   (function/forall
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['value (function/arrow 'A nnrat)]]
    nnrat)
   :value
   (function/lam
    [['A type-u] ['source (exact-finset-of 'A)]
     ['mass (function/arrow 'A nnrat)]
     ['value (function/arrow 'A nnrat)]]
    (map-sum
     'A
     (function/lam
      [['state 'A]]
      (multiply (function/app 'value 'state)
                (function/app 'mass 'state)))
     (enumeration 'A 'source)))})

(def definition-specs [list-map-sum-spec expectation-spec])

(def list-map-sum-respects-equivalence-spec
  (let [pointwise
        (function/forall
         [['value 'A]]
         (equivalent (function/app 'left 'value)
                     (function/app 'right 'value)))
        motive
        (function/lam
         [['source (list-of 'A)]]
         (equivalent (map-sum 'A 'left 'source)
                     (map-sum 'A 'right 'source)))]
    {:name 'list/nnrat-map-sum-respects-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['same pointwise]
       ['source (list-of 'A)]]
      (function/app motive 'source))
     :value
     (function/lam
      [['A type-u]
       ['left (function/arrow 'A nnrat)]
       ['right (function/arrow 'A nnrat)]
       ['same pointwise]
       ['source (list-of 'A)]]
      (function/app
       (function/const* 'data/List.rec [data-level zero-level])
       'A motive
       (function/app
        (function/const* 'nnrat/equivalent-reflexive []) nnrat-zero)
       (function/lam
        [['head 'A] ['tail (list-of 'A)]
         ['induction-hypothesis (function/app motive 'tail)]]
        (function/app
         (function/const* 'nnrat/add-respects-equivalence [])
         (function/app 'left 'head)
         (function/app 'right 'head)
         (map-sum 'A 'left 'tail)
         (map-sum 'A 'right 'tail)
         (function/app 'same 'head)
         'induction-hypothesis))
       'source))}))

(def finite-expectation-respects-equivalence-spec
  (let [mass-equivalence
        (function/forall
         [['state 'A]]
         (equivalent (function/app 'mass 'state)
                     (function/app 'equivalent-mass 'state)))
        value-equivalence
        (function/forall
         [['state 'A]]
         (equivalent (function/app 'value 'state)
                     (function/app 'equivalent-value 'state)))]
    {:name 'nnrat/finite-expectation-respects-equivalence
     :universes ['u]
     :type
     (function/forall
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nnrat)]
       ['equivalent-mass (function/arrow 'A nnrat)]
       ['value (function/arrow 'A nnrat)]
       ['equivalent-value (function/arrow 'A nnrat)]
       ['same-mass mass-equivalence]
       ['same-value value-equivalence]]
      (equivalent
       (expectation 'A 'source 'mass 'value)
       (expectation 'A 'source 'equivalent-mass 'equivalent-value)))
     :value
     (function/lam
      [['A type-u] ['source (exact-finset-of 'A)]
       ['mass (function/arrow 'A nnrat)]
       ['equivalent-mass (function/arrow 'A nnrat)]
       ['value (function/arrow 'A nnrat)]
       ['equivalent-value (function/arrow 'A nnrat)]
       ['same-mass mass-equivalence]
       ['same-value value-equivalence]]
      (let [left-mapping
            (function/lam
             [['state 'A]]
             (multiply (function/app 'value 'state)
                       (function/app 'mass 'state)))
            right-mapping
            (function/lam
             [['state 'A]]
             (multiply (function/app 'equivalent-value 'state)
                       (function/app 'equivalent-mass 'state)))
            same-products
            (function/lam
             [['state 'A]]
             (function/app
              (function/const* 'nnrat/multiply-respects-equivalence [])
              (function/app 'value 'state)
              (function/app 'equivalent-value 'state)
              (function/app 'mass 'state)
              (function/app 'equivalent-mass 'state)
              (function/app 'same-value 'state)
              (function/app 'same-mass 'state)))]
        (function/app
         (function/const* 'list/nnrat-map-sum-respects-equivalence [U])
         'A left-mapping right-mapping same-products
         (enumeration 'A 'source))))}))

(def theorem-specs
  [list-map-sum-respects-equivalence-spec
   finite-expectation-respects-equivalence-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Finite rational expectation expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn- add-spec [checked-environment spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind (if definition? :definition :theorem)
          :rainbow/aliases #{(:name spec)}
          :rainbow/universes (:universes spec)
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if definition? :reducible :opaque)
          :rainbow/dependencies (into (term/constants type)
                                      (term/constants value))
          :rainbow/provenance
          {:origin :native :producer :finite-rational-expectation}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Finite rational expectation declaration rejected"
                      {:name (:name spec) :result result})))
    (:environment result)))

(defn extend-definitions [checked-environment]
  (reduce add-spec checked-environment definition-specs))

(defn extend-theorems [checked-environment]
  (reduce add-spec checked-environment theorem-specs))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment extend-definitions extend-theorems))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.finite.rational-expectation))
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
