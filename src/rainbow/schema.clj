(ns rainbow.schema
  "Pure data schemas with deterministic, path-specific explanations."
  (:refer-clojure :exclude [boolean?])
  (:require [clojure.set :as set]))

(defn- actual-type [value]
  (cond
    (nil? value) :nil
    (clojure.core/boolean? value) :boolean
    (integer? value) :integer
    (number? value) :number
    (string? value) :string
    (keyword? value) :keyword
    (symbol? value) :symbol
    (uuid? value) :uuid
    (vector? value) :vector
    (map? value) :map
    (set? value) :set
    (sequential? value) :sequence
    :else (symbol (.getName (class value)))))

(defn- issue [path category expected value & [detail]]
  (merge {:path (vec path)
          :category category
          :expected expected
          :actual (actual-type value)}
         detail))

(defn- primitive-valid? [schema value]
  (case schema
    :any true
    :nil (nil? value)
    :boolean (clojure.core/boolean? value)
    :integer (integer? value)
    :natural (and (integer? value) (not (neg? value)))
    :number (number? value)
    :string (string? value)
    :keyword (keyword? value)
    :symbol (symbol? value)
    :uuid (uuid? value)
    :vector (vector? value)
    :map (map? value)
    :set (set? value)
    false))

(declare walk)

(defn- walk-map [descriptor value path options]
  (if-not (map? value)
    [(issue path :schema/type :map value)]
    (let [required (or (:required descriptor) {})
          optional (or (:optional descriptor) {})
          known (into (set (keys required)) (keys optional))
          missing (sort-by pr-str (set/difference (set (keys required)) (set (keys value))))
          unknown (when (:closed? descriptor)
                    (sort-by pr-str (set/difference (set (keys value)) known)))]
      (vec
       (concat
        (map #(issue (conj path %) :schema/missing-key (get required %) nil
                     {:key %})
             missing)
        (map #(issue (conj path %) :schema/unknown-key :absent (get value %)
                     {:key %})
             unknown)
        (mapcat (fn [[key schema]]
                  (when (contains? value key)
                    (walk schema (get value key) (conj path key) options)))
                (sort-by (comp pr-str key) (concat required optional))))))))

(defn- walk-collection [kind predicate item-schema descriptor value path options]
  (if-not (predicate value)
    [(issue path :schema/type kind value)]
    (let [size (count value)
          minimum (:min descriptor)
          maximum (:max descriptor)
          size-issues
          (concat
           (when (and minimum (< size minimum))
             [(issue path :schema/min-count minimum value {:count size})])
           (when (and maximum (> size maximum))
             [(issue path :schema/max-count maximum value {:count size})]))
          entries (if (set? value) (sort-by pr-str value) value)]
      (vec (concat size-issues
                   (mapcat (fn [index item]
                             (walk item-schema item (conj path index) options))
                           (range) entries))))))

(defn- walk-predicate [predicate-id value path options]
  (if-let [predicate (get-in options [:predicates predicate-id])]
    (try
      (if (true? (predicate value))
        []
        [(issue path :schema/predicate predicate-id value)])
      (catch Exception exception
        [(issue path :schema/predicate-exception predicate-id value
                {:exception/class (str (class exception))
                 :exception/message (ex-message exception)})]))
    [(issue path :schema/unknown-predicate predicate-id value)]))

(defn- walk [schema value path options]
  (cond
    (keyword? schema)
    (if (primitive-valid? schema value)
      []
      [(issue path :schema/type schema value)])

    (not (vector? schema))
    [(issue path :schema/invalid-schema :schema-form schema)]

    :else
    (case (first schema)
      :literal (if (= (second schema) value)
                 []
                 [(issue path :schema/literal (second schema) value)])

      :enum (let [members (set (second schema))]
              (if (contains? members value)
                []
                [(issue path :schema/enum members value)]))

      :maybe (if (nil? value) [] (walk (second schema) value path options))

      :vector (walk-collection :vector vector? (second schema) (or (nth schema 2 nil) {})
                               value path options)

      :set (walk-collection :set set? (second schema) (or (nth schema 2 nil) {})
                            value path options)

      :map (walk-map (second schema) value path options)

      :map-of
      (let [[_ key-schema value-schema constraints] schema]
        (if-not (map? value)
          [(issue path :schema/type :map value)]
          (let [size (count value)
                size-issues
                (concat
                 (when (and (:min constraints) (< size (:min constraints)))
                   [(issue path :schema/min-count (:min constraints) value {:count size})])
                 (when (and (:max constraints) (> size (:max constraints)))
                   [(issue path :schema/max-count (:max constraints) value {:count size})]))]
            (vec
             (concat
              size-issues
              (mapcat (fn [[key item]]
                        (concat
                         (walk key-schema key (conj path key :map-key) options)
                         (walk value-schema item (conj path key) options)))
                      (sort-by (comp pr-str key) value)))))))

      :tuple (let [schemas (vec (rest schema))]
               (if-not (vector? value)
                 [(issue path :schema/type :vector value)]
                 (if-not (= (count schemas) (count value))
                   [(issue path :schema/tuple-count (count schemas) value
                           {:count (count value)})]
                   (vec (mapcat (fn [index child-schema]
                                  (walk child-schema (nth value index)
                                        (conj path index) options))
                                (range) schemas)))))

      :or (let [alternatives (rest schema)
                results (mapv #(walk % value path options) alternatives)]
            (if (some empty? results)
              []
              [(issue path :schema/no-alternative alternatives value
                      {:alternatives (mapv first results)})]))

      :and (vec (mapcat #(walk % value path options) (rest schema)))

      :ref (if-let [resolved (get-in options [:registry (second schema)])]
             (walk resolved value path options)
             [(issue path :schema/unknown-reference (second schema) value)])

      :predicate (walk-predicate (second schema) value path options)

      :range (let [[_ base constraints] schema
                   base-issues (walk base value path options)]
               (if (seq base-issues)
                 base-issues
                 (vec
                  (concat
                   (when (and (contains? constraints :min)
                              (< value (:min constraints)))
                     [(issue path :schema/minimum (:min constraints) value)])
                   (when (and (contains? constraints :max)
                              (> value (:max constraints)))
                     [(issue path :schema/maximum (:max constraints) value)])))))

      :tagged-map
      (let [[_ tag-key cases] schema]
        (if-not (map? value)
          [(issue path :schema/type :map value)]
          (let [tag (get value tag-key ::missing)]
            (if-let [selected (get cases tag)]
              (walk selected value path options)
              [(issue (conj path tag-key) :schema/tag (set (keys cases))
                      (when-not (= ::missing tag) tag))]))))

      :tagged-vector
      (let [[_ cases] schema]
        (if-not (and (vector? value) (seq value))
          [(issue path :schema/tagged-vector :nonempty-vector value)]
          (if-let [selected (get cases (first value))]
            (walk selected value path options)
            [(issue (conj path 0) :schema/tag (set (keys cases)) (first value))])))

      [(issue path :schema/unknown-form (first schema) value)])))

(defn explain
  ([schema value] (explain schema value {}))
  ([schema value options]
   (walk schema value [] (merge {:registry {} :predicates {}} options))))

(defn valid?
  ([schema value] (empty? (explain schema value)))
  ([schema value options] (empty? (explain schema value options))))

(defn validate!
  ([schema value] (validate! schema value {}))
  ([schema value options]
   (let [issues (explain schema value options)]
     (if (empty? issues)
       value
       (throw (ex-info "Value does not conform to schema"
                       {:error/category :schema/invalid
                        :issues issues}))))))
