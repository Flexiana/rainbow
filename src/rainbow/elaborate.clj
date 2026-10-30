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

(def binder-modes #{:explicit :implicit})

(defn- valid-binder? [binder]
  (and (vector? binder)
       (contains? #{2 3} (count binder))
       (symbol? (first binder))
       (or (= 2 (count binder))
           (contains? binder-modes (nth binder 2)))))

(defn- elaborate-arrow
  "`[:-> A B ...]` through `elaborate`, which is `elaborate*` or `core*`."
  [elaborate environment arguments context]
  (when (< (count arguments) 2)
    (reject! :elaborate/arrow-arity "An arrow needs at least a domain and codomain"
             {:arguments arguments}))
  (let [domain (elaborate environment (first arguments) context)
        remaining (next arguments)
        body (if (= 1 (count remaining))
               (first remaining)
               (into [:->] remaining))]
    (term/pi-term domain (elaborate environment body (into [nil] context)))))

(defn- elaborate-binders [elaborate environment operation bindings body context]
  (if-let [[name type-surface mode] (first bindings)]
    (operation
     (elaborate environment type-surface context)
     (elaborate-binders elaborate environment operation (next bindings) body
                        (into [name] context))
     (or mode :explicit))
    (elaborate environment body context)))

(defn- elaborate*
  "Surface types without constants; `_environment` is unused (the shared arrow and
  binder helpers pass one)."
  [_environment surface context]
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
      :-> (elaborate-arrow elaborate* nil (rest surface) context)
      :forall (let [[_ bindings body] surface]
                (when-not (and (= 3 (count surface))
                               (vector? bindings)
                               (every? valid-binder? bindings))
                  (reject! :elaborate/invalid-forall "Malformed forall form" {:form surface}))
                (elaborate-binders elaborate* nil term/pi-term bindings body context))
      (reject! :elaborate/unsupported-form "Unsupported surface form" {:form surface}))

    :else
    (reject! :elaborate/unsupported-form "Unsupported surface value" {:form surface})))

(defn type-expression [surface]
  (try
    {:status :elaborated
     :surface surface
     :term (elaborate* nil surface [])
     :trace [{:operation :surface-to-core :input surface}]}
    (catch clojure.lang.ExceptionInfo exception
      {:status :rejected
       :error (ex-data exception)
       :message (ex-message exception)})))

(defn- core* [environment surface context]
  ;; Explicit work/value stacks keep surface depth off the JVM call stack.
  ;; Children are visited left to right, preserving the first reported error.
  (loop [work [[:visit surface context]] values []]
    (if (empty? work)
      (peek values)
      (let [[operation a b c d] (peek work)
            work (pop work)]
        (case operation
          :application
          (let [start (- (count values) a)
                children (subvec values start)]
            (recur work (conj (subvec values 0 start)
                              (reduce term/application (first children) (rest children)))))

          :binder
          (let [body (peek values) values (pop values)
                type (peek values) values (pop values)]
            (recur work (conj values (a type body b))))

          :let
          (let [body (peek values) values (pop values)
                value (peek values) values (pop values)
                type (peek values) values (pop values)]
            (recur work (conj values (term/let-term type value body))))

          :bindings
          (if-let [[name type mode] (first b)]
            (recur (conj work [:binder a (or mode :explicit)]
                              [:bindings a (next b) c (into [name] d)]
                              [:visit type d]) values)
            (recur (conj work [:visit c d]) values))

          :arrow
          (let [remaining (next a)
                next-context (into [nil] b)]
            (recur (conj work [:binder term/pi-term :explicit]
                              (if (= 1 (count remaining))
                                [:visit (first remaining) next-context]
                                [:arrow remaining next-context])
                              [:visit (first a) b]) values))

          :visit
          (let [surface a context b]
            (cond
              (= 'Prop surface)
              (recur work (conj values (term/sort-term term/zero-level)))

              (symbol? surface)
              (if-some [index (variable-index context surface)]
                (recur work (conj values (term/bound index)))
                (reject! :elaborate/unknown-name "Unknown term name"
                         {:name surface :context (vec (remove nil? context))}))

              (vector? surface)
              (case (first surface)
                :sort
                (let [level (second surface)]
                  (when-not (and (= 2 (count surface)) (term/level? level))
                    (reject! :elaborate/invalid-sort "Malformed sort form" {:form surface}))
                  (recur work (conj values (term/sort-term level))))

                :nat
                (let [[_ n] surface]
                  (when-not (and (= 2 (count surface)) (integer? n) (not (neg? n)))
                    (reject! :elaborate/invalid-literal "A literal is [:nat n] with n a natural number"
                             {:form surface}))
                  (recur work (conj values [:nat n])))

                :const
                (let [[_ alias levels] surface
                      id (if (string? alias) alias (environment/resolve-id environment alias))]
                  (when-not (and (= 3 (count surface)) id (vector? levels)
                                 (every? term/level? levels))
                    (reject! :elaborate/unknown-constant "Unknown or malformed constant"
                             {:form surface :alias alias}))
                  (recur work (conj values (term/constant id levels))))

                :app
                (let [children (subvec surface 1)]
                  (when (< (count children) 2)
                    (reject! :elaborate/application-arity
                             "Application needs at least one argument" {:form surface}))
                  (recur (into (conj work [:application (count children)])
                               (map #(vector :visit % context) (rseq children))) values))

                :->
                (let [arguments (rest surface)]
                  (when (< (count arguments) 2)
                    (reject! :elaborate/arrow-arity "An arrow needs at least a domain and codomain"
                             {:arguments arguments}))
                  (recur (conj work [:arrow arguments context]) values))

                (:forall :fn)
                (let [[kind bindings body] surface]
                  (when-not (and (= 3 (count surface)) (vector? bindings)
                                 (every? valid-binder? bindings))
                    (if (= :forall kind)
                      (reject! :elaborate/invalid-forall "Malformed forall form" {:form surface})
                      (reject! :elaborate/invalid-lambda "Malformed lambda form" {:form surface})))
                  (recur (conj work [:bindings (if (= :forall kind) term/pi-term term/lambda-term)
                                    bindings body context]) values))

                :let
                (let [[_ name type value body] surface]
                  (when-not (and (= 5 (count surface)) (symbol? name))
                    (reject! :elaborate/invalid-let "Malformed let form" {:form surface}))
                  (recur (conj work [:let] [:visit body (into [name] context)]
                                    [:visit value context] [:visit type context]) values))

                (reject! :elaborate/unsupported-form "Unsupported explicit term form" {:form surface}))

              :else
              (reject! :elaborate/unsupported-form "Unsupported explicit term value" {:form surface}))))))))

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
