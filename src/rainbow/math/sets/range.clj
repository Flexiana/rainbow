(ns rainbow.math.sets.range
  "Lean-compatible Set range ordering and native finite-range laws."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.set :as finite-set]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def data-level [:succ U])
(def target-data-level [:succ V])
(def type-u [:sort data-level])
(def type-v [:sort target-data-level])

(defn- target-set-of [element]
  (function/app (function/const* 'set/Set [V]) element))

(defn- equality [carrier left right]
  (function/equality target-data-level carrier left right))

(defn- native-range [domain codomain mapping]
  (function/app (function/const* 'set/range [U V])
                domain codomain mapping))

(defn- lean-range [codomain domain mapping]
  (function/app (function/const* 'set/lean-range [U V])
                codomain domain mapping))

(defn- singleton [element selected]
  (function/app (function/const* 'set/singleton [V])
                element selected))

(defn- finite [element source]
  (function/app (function/const* 'set/finite [V]) element source))

(defn- subset [element small large]
  (function/app (function/const* 'set/subset [V])
                element small large))

(def lean-range-spec
  {:name 'set/lean-range
   :kind :definition
   :universes ['u 'v]
   :transparency :reducible
   :type
   (function/forall
    [['B type-v] ['A type-u] ['mapping (function/arrow 'A 'B)]]
    (target-set-of 'B))
   :value
   (function/lam
    [['B type-v] ['A type-u] ['mapping (function/arrow 'A 'B)]]
    (native-range 'A 'B 'mapping))})

(def finite-range-constant-spec
  (let [mapping (function/lam [['ignored 'A]] 'selected)
        small (lean-range 'B 'A mapping)
        large (singleton 'B 'selected)
        small-finite (finite 'B small)
        large-finite (finite 'B large)
        truth (proposition/truth)
        inclusion
        (function/lam
         [['value 'B] ['range-member (function/app small 'value)]]
         (function/app
          (function/const* 'proposition/use-witness [data-level])
          'A
          (function/lam
           [['source 'A]]
           (equality 'B 'selected 'value))
          (function/app large 'value)
          'range-member
          (function/lam
           [['source 'A]
            ['same (equality 'B 'selected 'value)]]
           (function/app
            (function/const* 'equality/symmetric [target-data-level])
            'B 'selected 'value 'same))))
        singleton-finite
        (proposition/backward-equivalence
         large-finite truth
         (function/app
          (function/const* 'set/finite-singleton-equivalence [V])
          'B 'selected)
         (function/const* 'proposition/trivial []))]
    {:name 'set/finite-range-constant
     :universes ['u 'v]
     :type
     (function/forall
      [['A type-u :implicit] ['B type-v :implicit]
       ['selected 'B :implicit]]
      small-finite)
     :value
     (function/lam
      [['A type-u :implicit] ['B type-v :implicit]
       ['selected 'B :implicit]]
      (function/app
       (function/const* 'set/finite-subset-preserved [V])
       'B small large inclusion singleton-finite))}))

(def constant-aliases
  {"Set.range"
   {:native/alias 'set/lean-range
    :native/level-transform :lean-set-range}})

(def definition-specs [lean-range-spec])
(def theorem-specs [finite-range-constant-spec])

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Set-range expression failed elaboration"
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
          {:origin :native :producer :finite-set-range-bridge}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Set-range declaration was rejected"
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
  (module/install-module checked-environment 'rainbow.math.sets.range))
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
