(ns rainbow.math.milestone-support
  "Shared environment plumbing for proved-milestone modules. Each milestone
  module supplies its definition and theorem specs (maps with :name, :type,
  :value, :universes, and optional :kind :definition) and delegates the kernel
  registration here, rather than repeating the boilerplate. This keeps the module
  namespaces small (the trusted base and the release compactness gate both bound
  total source size)."
  (:require [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(defn- elaborate! [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "Milestone expression failed elaboration"
                      {:expression expression :result result})))
    (:term result)))

(defn add-spec
  "Elaborates and kernel-checks one spec, adding it to the environment. A spec
  with `:kind :definition` is reducible; otherwise it is an opaque theorem. A spec
  without `:universes` has none."
  [checked-environment producer spec]
  (let [type (elaborate! checked-environment (:type spec))
        value (elaborate! checked-environment (:value spec))
        definition? (= :definition (:kind spec))
        result (kernel/add-declaration
                checked-environment
                {:rainbow/kind (if definition? :definition :theorem)
                 :rainbow/aliases #{(:name spec)}
                 :rainbow/universes (or (:universes spec) [])
                 :rainbow/type type :rainbow/value value
                 :rainbow/transparency (if definition? :reducible :opaque)
                 :rainbow/dependencies (into (term/constants type)
                                             (term/constants value))
                 :rainbow/provenance {:origin :native :producer producer}
                 :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Milestone declaration rejected"
                      {:name (:name spec) :producer producer :result result})))
    (:environment result)))

(defn extend-with
  "Adds every spec (definitions then theorems) to the environment under a
  producer tag."
  [checked-environment producer specs]
  (reduce (fn [env spec] (add-spec env producer spec)) checked-environment specs))

(defn add-spec-shared
  "Like add-spec, but SHARED-WORLD SAFE. An absent alias installs as
  usual. A present alias is compared by ELABORATED TYPE against the
  stored declaration: identical means skip -- the verbatim-duplicate
  case that otherwise forces marker-guarded chain entry -- while a
  DIFFERENT statement under the same alias throws, naming both
  producers and both types. Two proofs of one statement are
  interchangeable; two statements under one name are the D20-shape
  corruption and must never be resolved silently. A definition is also
  compared by kind and value: a different body is a different meaning."
  [checked-environment producer spec]
  (if-let [existing-id (environment/resolve-id checked-environment
                                               (:name spec))]
    (let [stored (environment/declaration checked-environment existing-id)
          candidate-type (elaborate! checked-environment (:type spec))]
      ;; Universe parameters are part of the statement: same type body
      ;; under different universe arity must refuse here, not fail later
      ;; at a use site with the wrong number of universe arguments.
      (if (and (= candidate-type (:rainbow/type stored))
               (= (vec (:universes spec))
                  (vec (:rainbow/universes stored))))
        ;; A theorem's proof is interchangeable; a DEFINITION's body is its meaning. A
        ;; definition under a present alias must be the same kind and the same value
        ;; (elaborated, so binder names do not matter), or definitionally equal to it.
        (if (or (= :definition (:kind spec)) (= :definition (:rainbow/kind stored)))
          (let [candidate-value (elaborate! checked-environment (:value spec))]
            (if (and (= :definition (:kind spec))
                     (= :definition (:rainbow/kind stored))
                     (or (= candidate-value (:rainbow/value stored))
                         (true? (kernel/definitionally-equal? checked-environment candidate-value
                                                              (:rainbow/value stored)))))
              checked-environment
              (throw (ex-info "Shared-world alias conflict: one alias, two definitions"
                              {:name (:name spec)
                               :incoming-producer producer
                               :existing-producer (get-in stored [:rainbow/provenance :producer])
                               :existing-kind (:rainbow/kind stored)
                               :incoming-kind (if (= :definition (:kind spec)) :definition :theorem)
                               :existing-value (:rainbow/value stored)
                               :incoming-value candidate-value}))))
          checked-environment)
        (throw (ex-info "Shared-world alias conflict: one alias, two statements"
                        {:name (:name spec)
                         :incoming-producer producer
                         :existing-producer
                         (get-in stored [:rainbow/provenance :producer])
                         :existing-type (:rainbow/type stored)
                         :existing-universes (:rainbow/universes stored)
                         :incoming-type candidate-type
                         :incoming-universes (:universes spec)}))))
    (add-spec checked-environment producer spec)))

(defn extend-with-shared
  "extend-with through add-spec-shared: duplicates skip, divergences
  throw."
  [checked-environment producer specs]
  (reduce (fn [env spec] (add-spec-shared env producer spec))
          checked-environment specs))

(defn spec-ids
  "Resolves each spec's :name to its content id, as a sorted map."
  [checked-environment specs]
  (into (sorted-map)
        (map (fn [spec]
               [(:name spec)
                (environment/resolve-id checked-environment (:name spec))]))
        specs))
