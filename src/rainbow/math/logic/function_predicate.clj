(ns rainbow.math.logic.function-predicate
  "Checked native declarations for reusable higher-order function predicates."
  (:require [rainbow.module :as module]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.function :as function]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.term :as term]))

(def U [:param 'u])
(def V [:param 'v])
(def sort-u [:sort U])
(def sort-v [:sort V])

(def predicate-specs
  [{:name 'function/involutive
    :universes ['u]
    :type
    (function/forall
     [['carrier sort-u]
      ['callable (function/arrow 'carrier 'carrier)]]
     'Prop)
    :value
    (function/lam
     [['carrier sort-u]
      ['callable (function/arrow 'carrier 'carrier)]]
     (function/involutive U 'carrier 'callable))}

   {:name 'function/injective
    :universes ['u 'v]
    :type
    (function/forall
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     'Prop)
    :value
    (function/lam
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     (function/injective U V 'domain 'codomain 'callable))}

   {:name 'function/surjective
    :universes ['u 'v]
    :type
    (function/forall
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     'Prop)
    :value
    (function/lam
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     (function/surjective U V 'domain 'codomain 'callable))}

   {:name 'function/bijective
    :universes ['u 'v]
    :type
    (function/forall
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     'Prop)
    :value
    (function/lam
     [['domain sort-u] ['codomain sort-v]
      ['callable (function/arrow 'domain 'codomain)]]
     (function/bijective U V 'domain 'codomain 'callable))}])

(defn- elaborate! [checked-environment surface]
  (let [result (elaborate/core-expression checked-environment surface)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Function predicate failed elaboration"
                      {:surface surface :result result})))
    (:term result)))

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (reduce (fn [environment spec] (let [type (elaborate! environment (:type spec)) value (elaborate! environment (:value spec)) added (kernel/add-declaration environment {:rainbow/kind :definition :rainbow/aliases #{(:name spec)} :rainbow/universes (:universes spec) :rainbow/type type :rainbow/value value :rainbow/transparency :reducible :rainbow/dependencies (into (term/constants type) (term/constants value)) :rainbow/provenance {:origin :native :producer :function-predicate-data} :rainbow/schema-version 1})] (when-not (= :accepted (:status added)) (throw (ex-info "Function predicate declaration rejected" {:name (:name spec) :result added}))) (:environment added))) checked-environment predicate-specs))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.logic.function-predicate))
(defn build-environment []
  (extend-environment (proposition/build-environment)))

(defn report []
  (let [checked-environment (build-environment)]
    {:status :passed
     :predicates (mapv :name predicate-specs)
     :axioms
     (into {} (map (fn [{:keys [name]}]
                     [name (kernel/axioms checked-environment name)]))
           predicate-specs)
     :trusted-base-change :none}))
