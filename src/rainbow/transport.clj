(ns rainbow.transport
  "Untrusted validation of checked theory and representation mappings. A
  transport record organizes kernel-checked adapters and laws; it is not a new
  kernel rule."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(def schema-version 1)
(def relations
  #{:definitionally-equal :logically-equivalent :rainbow-generalizes
    :rainbow-specializes :representation-refinement
    :assumption-preserving-translation})

(defn- reject [category detail]
  {:status :rejected :error (assoc detail :error/category category)})

(defn semantic-content [mapping]
  (select-keys mapping
               [:transport/schema-version :transport/relation
                :transport/source :transport/target :transport/forward
                :transport/backward :transport/laws
                :transport/transported-theorems]))

(defn transport-id [mapping]
  (canonical/content-id (semantic-content mapping)))

(defn- checked-declaration [checked-environment id-or-alias]
  (when-let [id (environment/resolve-id checked-environment id-or-alias)]
    (let [declaration (environment/declaration checked-environment id)
          checked (kernel/check checked-environment
                                (:rainbow/value declaration)
                                (:rainbow/type declaration)
                                (set (:rainbow/universes declaration)))]
      (when (= :checked (:status checked)) declaration))))

(defn validate
  "Checks adapter signatures and rechecks every law/theorem declaration. The
  caller supplies the expected source/target core types as immutable data."
  [checked-environment mapping]
  (let [source (get-in mapping [:transport/source :type])
        target (get-in mapping [:transport/target :type])
        forward (checked-declaration checked-environment (:transport/forward mapping))
        backward (checked-declaration checked-environment (:transport/backward mapping))
        expected-forward (when (and source target) (term/pi-term source target))
        expected-backward (when (and source target) (term/pi-term target source))
        laws (mapv #(checked-declaration checked-environment %)
                   (vals (:transport/laws mapping)))
        transported (mapv #(checked-declaration checked-environment
                                                (:target/theorem-id %))
                          (:transport/transported-theorems mapping))]
    (cond
      (not= schema-version (:transport/schema-version mapping))
      (reject :transport/schema-version
              {:actual (:transport/schema-version mapping)})

      (not (contains? relations (:transport/relation mapping)))
      (reject :transport/unsupported-relation
              {:relation (:transport/relation mapping)})

      (not (and (term/term? source) (term/term? target)))
      (reject :transport/invalid-representation-types {})

      (nil? forward)
      (reject :transport/unchecked-forward
              {:declaration (:transport/forward mapping)})

      (nil? backward)
      (reject :transport/unchecked-backward
              {:declaration (:transport/backward mapping)})

      (not (true? (kernel/definitionally-equal?
                   checked-environment (:rainbow/type forward) expected-forward)))
      (reject :transport/forward-type
              {:expected expected-forward :actual (:rainbow/type forward)})

      (not (true? (kernel/definitionally-equal?
                   checked-environment (:rainbow/type backward) expected-backward)))
      (reject :transport/backward-type
              {:expected expected-backward :actual (:rainbow/type backward)})

      (or (empty? laws) (some nil? laws))
      (reject :transport/unchecked-law {:laws (:transport/laws mapping)})

      (some nil? transported)
      (reject :transport/unchecked-transported-theorem
              {:theorems (:transport/transported-theorems mapping)})

      :else
      (let [id (transport-id mapping)]
        {:status :checked
         :transport/id id
         :mapping (assoc mapping :transport/id id :transport/status :checked)
         :kernel-rechecks (+ 2 (count laws) (count transported))
         :axioms (into #{}
                       (mapcat #(kernel/axioms checked-environment (:rainbow/id %)))
                       (concat [forward backward] laws transported))}))))
