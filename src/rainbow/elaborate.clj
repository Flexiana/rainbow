(ns rainbow.elaborate
  "Small deterministic surface-to-core elaborator for explicit function propositions."
  (:require [rainbow.environment :as environment]
            [rainbow.term :as term]))

(defn- reject! [category message data]
  (throw (ex-info message (assoc data :error/category category))))

(defn- variable-index [context name]
  (first (keep-indexed (fn [index candidate]
                         (when (= name candidate) index))
                       context)))

(declare elaborate*)

(def binder-modes #{:explicit :implicit})

(defn- valid-binder? [binder]
  (and (vector? binder)
       (contains? #{2 3} (count binder))
       (symbol? (first binder))
       (or (= 2 (count binder))
           (contains? binder-modes (nth binder 2)))))

(defn- elaborate-arrow [arguments context]
  (when (< (count arguments) 2)
    (reject! :elaborate/arrow-arity "An arrow needs at least a domain and codomain"
             {:arguments arguments}))
  (let [domain (elaborate* (first arguments) context)
        remaining (next arguments)
        body-surface (if (= 1 (count remaining))
                       (first remaining)
                       (into [:->] remaining))]
    (term/pi-term domain (elaborate* body-surface (into [nil] context)))))

(defn- elaborate-forall [bindings body context]
  (if-let [[name type-surface mode] (first bindings)]
    (do
      (when-not (symbol? name)
        (reject! :elaborate/invalid-binder "Binder name must be a symbol"
                 {:binder (first bindings)}))
      (term/pi-term
       (elaborate* type-surface context)
       (elaborate-forall (next bindings) body (into [name] context))
       (or mode :explicit)))
    (elaborate* body context)))

(defn- elaborate* [surface context]
  (cond
    (= 'Prop surface) (term/sort-term term/zero-level)

    (symbol? surface)
    (if-some [index (variable-index context surface)]
      (term/bound index)
      (reject! :elaborate/unknown-name "Unknown surface name"
               {:name surface :context (vec (remove nil? context))}))

    (vector? surface)
    (case (first surface)
      :sort (let [level (second surface)]
              (when-not (and (= 2 (count surface)) (term/level? level))
                (reject! :elaborate/invalid-sort "Malformed sort form" {:form surface}))
              (term/sort-term level))
      :-> (elaborate-arrow (rest surface) context)
      :forall (let [[_ bindings body] surface]
                (when-not (and (= 3 (count surface))
                               (vector? bindings)
                               (every? valid-binder? bindings))
                  (reject! :elaborate/invalid-forall "Malformed forall form" {:form surface}))
                (elaborate-forall bindings body context))
      (reject! :elaborate/unsupported-form "Unsupported surface form" {:form surface}))

    :else
    (reject! :elaborate/unsupported-form "Unsupported surface value" {:form surface})))

(defn type-expression [surface]
  (try
    {:status :elaborated
     :surface surface
     :term (elaborate* surface [])
     :trace [{:operation :surface-to-core :input surface}]}
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(declare core*)

(defn- core-arrow [environment arguments context]
  (when (< (count arguments) 2)
    (reject! :elaborate/arrow-arity "An arrow needs at least a domain and codomain"
             {:arguments arguments}))
  (let [domain (core* environment (first arguments) context)
        remaining (next arguments)
        body (if (= 1 (count remaining))
               (first remaining)
               (into [:->] remaining))]
    (term/pi-term domain (core* environment body (into [nil] context)))))

(defn- core-binders [environment operation bindings body context]
  (if-let [[name type-surface mode] (first bindings)]
    (do
      (when-not (symbol? name)
        (reject! :elaborate/invalid-binder "Binder name must be a symbol"
                 {:binder (first bindings)}))
      (operation
       (core* environment type-surface context)
       (core-binders environment operation (next bindings) body
                     (into [name] context))
       (or mode :explicit)))
    (core* environment body context)))

(defn- core* [environment surface context]
  (cond
    (= 'Prop surface) (term/sort-term term/zero-level)

    (symbol? surface)
    (if-some [index (variable-index context surface)]
      (term/bound index)
      (reject! :elaborate/unknown-name "Unknown term name"
               {:name surface :context (vec (remove nil? context))}))

    (vector? surface)
    (case (first surface)
      :sort (let [level (second surface)]
              (when-not (and (= 2 (count surface)) (term/level? level))
                (reject! :elaborate/invalid-sort "Malformed sort form" {:form surface}))
              (term/sort-term level))

      ;; a natural-number literal (the kernel types it as data/Nat)
      :nat (let [[_ n] surface]
             (when-not (and (= 2 (count surface)) (integer? n) (not (neg? n)))
               (reject! :elaborate/invalid-literal "A literal is [:nat n] with n a natural number"
                        {:form surface}))
             [:nat n])

      :const (let [[_ alias levels] surface
                   id (if (string? alias) alias (environment/resolve-id environment alias))]
               (when-not (and (= 3 (count surface)) id (vector? levels)
                              (every? term/level? levels))
                 (reject! :elaborate/unknown-constant "Unknown or malformed constant"
                          {:form surface :alias alias}))
               (term/constant id levels))

      :app (let [[_ function & arguments] surface]
             (when (empty? arguments)
               (reject! :elaborate/application-arity
                        "Application needs at least one argument" {:form surface}))
             (reduce term/application
                     (core* environment function context)
                     (map #(core* environment % context) arguments)))

      :-> (core-arrow environment (rest surface) context)

      :forall (let [[_ bindings body] surface]
                (when-not (and (= 3 (count surface)) (vector? bindings)
                               (every? valid-binder? bindings))
                  (reject! :elaborate/invalid-forall "Malformed forall form" {:form surface}))
                (core-binders environment term/pi-term bindings body context))

      :fn (let [[_ bindings body] surface]
            (when-not (and (= 3 (count surface)) (vector? bindings)
                           (every? valid-binder? bindings))
              (reject! :elaborate/invalid-lambda "Malformed lambda form" {:form surface}))
            (core-binders environment term/lambda-term bindings body context))

      :let (let [[_ name type-surface value body] surface]
             (when-not (and (= 5 (count surface)) (symbol? name))
               (reject! :elaborate/invalid-let "Malformed let form" {:form surface}))
             (term/let-term (core* environment type-surface context)
                            (core* environment value context)
                            (core* environment body (into [name] context))))

      (reject! :elaborate/unsupported-form "Unsupported explicit term form"
               {:form surface}))

    :else
    (reject! :elaborate/unsupported-form "Unsupported explicit term value"
             {:form surface})))

(defn core-expression [environment surface]
  (try
    {:status :elaborated
     :surface surface
     :term (core* environment surface [])
     :trace [{:operation :explicit-core-elaboration :input surface}]}
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))
