(ns rainbow.persistence
  "Persistence boundary for checked declarations. Loading always re-enters the kernel."
  (:require [clojure.edn :as edn]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.schemas :as schemas]))

(def artifact-schema-version 1)

(defn- block-alias-variants [environment aliases-by-id block-id]
  ;; Adding another alias set for an existing block retains navigation aliases,
  ;; but its stored spec/member metadata describes only the most recent set.
  ;; Reconstruct disjoint alias sets, keeping that latest set last. Every emitted
  ;; variant still goes through add-inductive-block during replay.
  (let [block (environment/block environment block-id)
        spec (:block/spec block)
        members (butlast (:block/member-ids block))
        latest (into [(:block/alias spec)] (map :constructor/alias (:block/constructors spec)))
        aliases (mapv (fn [id current]
                        (conj (vec (sort-by str (disj (get aliases-by-id id #{}) current)))
                              current))
                      members latest)]
    (when-not (apply = (map count aliases))
      (throw (ex-info "Inductive member alias sets have inconsistent sizes"
                      {:block-id block-id})))
    (mapv (fn [i]
            (-> spec
                (assoc :rainbow/id block-id :block/alias (get-in aliases [0 i]))
                (update :block/constructors
                        (fn [constructors]
                          (mapv (fn [j constructor]
                                  (assoc constructor :constructor/alias (get-in aliases [(inc j) i])))
                                (range) constructors)))))
          (range (count (first aliases))))))

(defn environment-artifact [environment]
  (let [aliases-by-id (reduce-kv (fn [m alias id] (update m id (fnil conj #{}) alias))
                                 {} (:rainbow.environment/aliases environment))
        block-ids (distinct (:rainbow.environment/block-order environment))
        variants (into {} (map (fn [id] [id (block-alias-variants environment aliases-by-id id)])
                               block-ids))
        declarations (into []
                           (comp (map #(environment/declaration environment %))
                                 (remove :rainbow/block-id))
                           (distinct (:rainbow.environment/order environment)))
        blocks (into [] (mapcat variants) block-ids)
        entries
        (into []
              (mapcat (fn [id]
                        (let [declaration (environment/declaration environment id)]
                          (cond
                            (not (:rainbow/block-id declaration))
                            [{:entry/kind :declaration :entry/value declaration}]

                            (= :inductive (:rainbow/member-key declaration))
                            (mapv #(hash-map :entry/kind :inductive-block :entry/value %)
                                  (get variants (:rainbow/block-id declaration)))

                            :else []))))
              (distinct (:rainbow.environment/order environment)))]
    {:rainbow.artifact/schema-version artifact-schema-version
     :rainbow.artifact/kind :checked-environment
     :rainbow.artifact/environment-id (environment/environment-id environment)
     :rainbow.artifact/declarations declarations
     :rainbow.artifact/inductive-blocks blocks
     :rainbow.artifact/entries entries}))

(defn save-environment! [environment path]
  (let [artifact (environment-artifact environment)]
    (binding [*print-namespace-maps* false
              *print-length* nil *print-level* nil
              *print-meta* false *print-dup* false *print-readably* true]
      (spit path (str (pr-str artifact) "\n")))
    {:status :saved
     :path (str path)
     :environment-id (:rainbow.artifact/environment-id artifact)
     :declarations (count (:rainbow.environment/declarations environment))
     :inductive-blocks (count (:rainbow.artifact/inductive-blocks artifact))}))

(defn replay-artifact [artifact]
  (let [schema-issues (schemas/explain-environment-artifact artifact)]
    (cond
      (seq schema-issues)
      {:status :rejected
       :error {:error/category :persistence/schema-rejected
               :issues schema-issues}}

      (not= artifact-schema-version (:rainbow.artifact/schema-version artifact))
    {:status :rejected
     :error {:error/category :persistence/unsupported-schema
             :actual (:rainbow.artifact/schema-version artifact)}}

      :else
      (let [entries (or (:rainbow.artifact/entries artifact)
                        (into (mapv #(hash-map :entry/kind :declaration :entry/value %)
                                    (:rainbow.artifact/declarations artifact))
                              (map #(hash-map :entry/kind :inductive-block :entry/value %)
                                   (:rainbow.artifact/inductive-blocks artifact))))]
        (loop [current (environment/empty-environment)
               remaining entries]
          (if-let [{:entry/keys [kind value]} (first remaining)]
            (let [result (case kind
                           :declaration (kernel/add-declaration current value)
                           :inductive-block (kernel/add-inductive-block current value))]
              (if (= :accepted (:status result))
                (recur (:environment result) (next remaining))
                {:status :rejected
                 :error {:error/category (if (= :inductive-block kind)
                                           :persistence/inductive-block-rejected
                                           :persistence/declaration-rejected)
                         :entry/id (:rainbow/id value)
                         :cause result}}))
            (let [actual-id (environment/environment-id current)
                  expected-id (:rainbow.artifact/environment-id artifact)]
              (if (= expected-id actual-id)
                {:status :replayed :environment current :environment-id actual-id}
                {:status :rejected
                 :error {:error/category :persistence/environment-id-mismatch
                         :expected expected-id :actual actual-id}}))))))))

(defn load-environment [path]
  (try
    (replay-artifact (edn/read-string (slurp path)))
    (catch Exception exception
      {:status :rejected
       :error {:error/category :persistence/malformed-artifact
               :class (str (class exception))}
       :message (.getMessage exception)})))
