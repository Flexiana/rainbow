(ns rainbow.kernel-speedup-reference.environment
  "Immutable declaration environments. Names are navigation aliases, never identity."
  (:require [rainbow.kernel-speedup-reference.canonical :as canonical]))

(def schema-version 1)

(defn empty-environment []
  {:rainbow.environment/schema-version schema-version
   :rainbow.environment/declarations {}
   :rainbow.environment/aliases {}
   :rainbow.environment/order []
   :rainbow.environment/blocks {}
   :rainbow.environment/block-order []})

(defn declaration [environment id]
  (get-in environment [:rainbow.environment/declarations id]))

(defn resolve-id [environment id-or-alias]
  (cond
    (and (string? id-or-alias) (declaration environment id-or-alias)) id-or-alias
    (symbol? id-or-alias) (get-in environment [:rainbow.environment/aliases id-or-alias])
    :else nil))

(defn semantic-declaration [declaration]
  (select-keys declaration [:rainbow/kind
                            :rainbow/universes
                            :rainbow/type
                            :rainbow/value
                            :rainbow/transparency
                            :rainbow/dependencies
                            :rainbow/block-id
                            :rainbow/member-key
                            :rainbow/schema-version]))

(defn declaration-id [declaration]
  (if-let [block-id (:rainbow/block-id declaration)]
    (canonical/content-id {:block/id block-id
                           :block/member-key (:rainbow/member-key declaration)})
    (canonical/content-id (semantic-declaration declaration))))

(defn block [environment id]
  (get-in environment [:rainbow.environment/blocks id]))

(defn environment-id [environment]
  (let [blocks (vec (sort (keys (:rainbow.environment/blocks environment))))
        base {:schema-version schema-version
              :declarations (vec (sort (keys (:rainbow.environment/declarations environment))))}]
    (canonical/content-id (cond-> base (seq blocks) (assoc :blocks blocks)))))
