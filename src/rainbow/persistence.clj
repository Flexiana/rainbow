(ns rainbow.persistence
  "Persistence boundary for checked declarations. Loading always re-enters the kernel."
  (:require [clojure.edn :as edn]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.schemas :as schemas]))

(def artifact-schema-version 1)

(defn environment-artifact [environment]
  (let [declarations
        (into []
              (keep (fn [id]
                      (let [declaration (environment/declaration environment id)]
                        (when-not (:rainbow/block-id declaration) declaration))))
              (:rainbow.environment/order environment))
        blocks (mapv (fn [id]
                       (let [block (environment/block environment id)]
                         (assoc (:block/spec block) :rainbow/id id)))
                     (:rainbow.environment/block-order environment))
        entries
        (into []
              (keep (fn [id]
                      (let [declaration (environment/declaration environment id)]
                        (cond
                          (not (:rainbow/block-id declaration))
                          {:entry/kind :declaration :entry/value declaration}

                          (= :inductive (:rainbow/member-key declaration))
                          (let [block (environment/block environment
                                                         (:rainbow/block-id declaration))]
                            {:entry/kind :inductive-block
                             :entry/value (assoc (:block/spec block)
                                                 :rainbow/id (:rainbow/id block))})

                          :else nil))))
              (:rainbow.environment/order environment))]
    {:rainbow.artifact/schema-version artifact-schema-version
     :rainbow.artifact/kind :checked-environment
     :rainbow.artifact/environment-id (environment/environment-id environment)
     :rainbow.artifact/declarations declarations
     :rainbow.artifact/inductive-blocks blocks
     :rainbow.artifact/entries entries}))

(defn save-environment! [environment path]
  (let [artifact (environment-artifact environment)]
    (spit path (str (pr-str artifact) "\n"))
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
