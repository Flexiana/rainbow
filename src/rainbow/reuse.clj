(ns rainbow.reuse
  "Deterministic, policy-aware retrieval of checked theorem constants.

  Retrieval is untrusted: candidates become ordinary `:const` proof terms and
  the tactic/kernel boundary checks them in the current proof state."
  (:require [clojure.set :as set]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]
            [rainbow.canonical-stream :as canonical-stream]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.proof :as proof]
            [rainbow.term :as term]))

(def schema-version 1)

(defn environment-id [environment]   ; a search asks per state; remembered for the latest environment
  (proof/memoized ::environment-id environment nil #(environment/environment-id environment)))

(def default-policy
  {:allowed-axioms #{}
   :allowed-sources nil
   :denied-dependencies #{}
   :required-concepts #{}})

(defn- ordered-level-parameters
  "Returns universe parameters in first structural occurrence order."
  [expression]
  (letfn [(level-parameters [level]
            (case (first level)
              :zero []
              :param [(second level)]
              :succ (level-parameters (second level))
              (:max :imax) (concat (level-parameters (second level))
                                   (level-parameters (nth level 2)))))
          (term-parameters [node]
            (case (first node)
              :sort (level-parameters (second node))
              (:bound :nat) []
              :const (mapcat level-parameters (nth node 2))
              (:app :lam :pi) (concat (term-parameters (second node))
                                      (term-parameters (nth node 2)))
              :let (concat (term-parameters (second node))
                           (term-parameters (nth node 2))
                           (term-parameters (nth node 3)))))]
    (vec (distinct (term-parameters expression)))))

(defn- canonicalize-universe-parameters [expression parameters]
  (term/instantiate-universes
   expression
   (into {}
         (map-indexed
          (fn [index parameter]
            [parameter [:param (symbol (str "reuse-u" index))]])
          parameters))))

(defn- canonicalize-universe-dag
  "The same renaming, with a per-call identity cache. Normalization produces
  shared terms: expanding those back into a tree can exhaust the heap before
  hashing starts. Do not pass these large transient roots through the kernel's
  persistent per-thread empty-substitution cache."
  [expression parameters]
  (let [substitution (into {} (map-indexed (fn [i p] [p [:param (symbol (str "reuse-u" i))]]) parameters))
        memo (java.util.IdentityHashMap.)]
    (letfn [(walk [node]
              (or (.get memo node)
                  (let [result
                        (case (first node)
                          :sort [:sort (term/instantiate-level (second node) substitution)]
                          (:bound :nat) node
                          :const [:const (second node) (mapv #(term/instantiate-level % substitution) (nth node 2))]
                          :app [:app (walk (second node)) (walk (nth node 2))]
                          (:lam :pi) [(first node) (walk (second node)) (walk (nth node 2)) (nth node 3)]
                          :let [:let (walk (second node)) (walk (nth node 2)) (walk (nth node 3))])]
                    (.put memo node result)
                    result)))]
      (walk expression))))

(defn normalized-type-key
  "Content key modulo both term binders and universe-parameter names."
  ([checked-environment type]
   (normalized-type-key checked-environment type nil))
  ([checked-environment type universe-parameters]
   (normalized-type-key checked-environment type universe-parameters {}))
  ([checked-environment type universe-parameters {:keys [incremental? normal]}]
   (let [normalized (if normal {:status (if (normal) :normalized :rejected) :term (normal)}   ; a memoized normal form
                        (kernel/normalize checked-environment type))
         content-id (if incremental? canonical-stream/content-id-incremental canonical/content-id)]
     (when-not (= :normalized (:status normalized))
       (throw (ex-info "Cannot index a type that does not normalize"
                       {:error/category :reuse/normalization-failed
                        :cause normalized})))
     (let [normalized-type (:term normalized)
           parameters (or universe-parameters
                          (ordered-level-parameters normalized-type))]
       (content-id
        {:reuse/type
         ((if incremental? canonicalize-universe-dag canonicalize-universe-parameters)
          normalized-type parameters)})))))

(defn- alias-concepts [aliases]
  (into #{}
        (mapcat (fn [alias]
                  (keep (fn [token]
                          (when-not (string/blank? token)
                            (keyword "alias" token)))
                        (string/split (str alias) #"[/.-]"))))
        aliases))

(defn- shape-concepts [type]
  (into #{}
        (keep (fn [value]
                (when (and (vector? value) (keyword? (first value)))
                  (keyword "shape" (name (first value))))))
        (tree-seq coll? seq type)))

(defn- lifecycle-record [lifecycle declaration-id]
  (let [value (get lifecycle declaration-id :active)]
    (if (keyword? value) {:status value} value)))

(defn- declaration-entry [checked-environment declaration lifecycle evidence incremental?]
  (let [id (:rainbow/id declaration)
        lifecycle (lifecycle-record lifecycle id)
        type-universes
        (ordered-level-parameters (:rainbow/type declaration))
        concepts (into (shape-concepts (:rainbow/type declaration))
                       (alias-concepts (:rainbow/aliases declaration)))]
    {:reuse/declaration-id id
     :reuse/type-key (normalized-type-key checked-environment
                                         (:rainbow/type declaration)
                                         type-universes {:incremental? incremental?})
     :reuse/universes (:rainbow/universes declaration)
     :reuse/type-universes type-universes
     :reuse/aliases (:rainbow/aliases declaration)
     :reuse/concepts concepts
     :reuse/dependencies (:rainbow/dependencies declaration)
     :reuse/axioms (:rainbow/axioms declaration)
     :reuse/source (get-in declaration [:rainbow/provenance :origin] :unknown)
     :reuse/lifecycle lifecycle
     :reuse/evidence (merge {:successful-uses 0 :failed-uses 0}
                            (get evidence id))}))

(defn build-index
  "Builds immutable retrieval data from checked theorem declarations.

  `:include-ids` can hold out declarations from training. `:lifecycle` and
  `:evidence` are maps keyed by declaration ID; quarantined entries remain
  inspectable but are never returned. Universe-polymorphic constants are
  instantiated only when their named parameters occur in the exact target.
  `:incremental? true` streams normalized-type and index identity encodings;
  entries, schema and all existing :reuse/id values remain identical."
  ([checked-environment] (build-index checked-environment {}))
  ([checked-environment {:keys [include-ids lifecycle evidence incremental?]
                         :or {lifecycle {} evidence {}}}]
   (let [included? (if include-ids (set include-ids) (constantly true))
         candidates (->> (:rainbow.environment/order checked-environment)
                         (map #(environment/declaration checked-environment %))
                         (filter #(and (= :theorem (:rainbow/kind %))
                                       (:rainbow/value %)
                                       (included? (:rainbow/id %)))))
         ;; A declaration whose type cannot be normalized within the kernel
         ;; reduction budget is deterministically quarantined (with telemetry)
         ;; rather than aborting the whole index. Retrieval is untrusted -- the
         ;; kernel re-checks every candidate -- so dropping one from the index is
         ;; sound; it just is not offered for reuse. Any other error still throws.
         classified
         (mapv (fn [declaration]
                 (try
                   {:entry (declaration-entry checked-environment declaration
                                              lifecycle evidence incremental?)}
                   (catch clojure.lang.ExceptionInfo exception
                     (if (= :reuse/normalization-failed
                            (:error/category (ex-data exception)))
                       {:quarantined
                        {:reuse/declaration-id (:rainbow/id declaration)
                         :reuse/aliases (:rainbow/aliases declaration)
                         :reuse/quarantine-reason :normalization-resource-limit}}
                       (throw exception)))))
               candidates)
         entries (->> classified (keep :entry) (sort-by :reuse/declaration-id) vec)
         quarantined (->> classified (keep :quarantined)
                          (sort-by :reuse/declaration-id) vec)
         active (filter #(= :active (get-in % [:reuse/lifecycle :status])) entries)
         buckets (reduce (fn [result entry]
                           (update result (:reuse/type-key entry)
                                   (fnil conj []) (:reuse/declaration-id entry)))
                         (sorted-map) active)
         base {:reuse/schema-version schema-version
               :reuse/environment-id (environment/environment-id checked-environment)
               :reuse/entries entries
               :reuse/by-type buckets
               :reuse/quarantined quarantined}]
     (assoc base :reuse/id ((if incremental? canonical-stream/content-id-incremental
                               canonical/content-id) base)))))

(defn- eligible? [entry policy]
  (and (= :active (get-in entry [:reuse/lifecycle :status]))
       (set/subset? (:reuse/axioms entry) (:allowed-axioms policy))
       (or (nil? (:allowed-sources policy))
           (contains? (:allowed-sources policy) (:reuse/source entry)))
       (empty? (set/intersection (:reuse/dependencies entry)
                                 (:denied-dependencies policy)))
       (set/subset? (:required-concepts policy) (:reuse/concepts entry))))

(defn- term-level-params [value]
  (cond
    (and (vector? value) (= :sort (first value)))
    (term/level-params (second value))

    (and (vector? value) (= :const (first value)))
    (into #{} (mapcat term/level-params) (nth value 2))

    (coll? value)
    (into #{} (mapcat term-level-params) value)

    :else #{}))

(defn- reusable-in-target? [entry target-levels]
  (set/subset? (set (:reuse/universes entry)) target-levels))

(defn- reuse-term
  ([entry]
   (term/constant (:reuse/declaration-id entry)
                  (mapv (fn [parameter] [:param parameter])
                        (:reuse/universes entry))))
  ([entry target-universes]
   (let [substitution (zipmap (:reuse/type-universes entry)
                              target-universes)
         levels (mapv substitution (:reuse/universes entry))]
     (when (and (= (count (:reuse/type-universes entry))
                   (count target-universes))
                (every? some? levels))
       (term/constant (:reuse/declaration-id entry)
                      (mapv (fn [parameter] [:param parameter]) levels))))))

(def ^:private views (atom nil))
(defn- index-view
  "Lookups built once per index value: entries by id, each entry's shape-concept bits, and the
  eligible entry positions per [policy target-levels]."
  [index]
  (let [[latest view] @views]
    (if (identical? latest index) view
        (let [entries (:reuse/entries index)
              bits (zipmap (distinct (mapcat #(filter (comp #{"shape"} namespace) (:reuse/concepts %)) entries))
                           (map #(bit-shift-left 1 %) (range)))]
          (peek (reset! views [index {:by-id (into {} (map (juxt :reuse/declaration-id identity)) entries) :bits bits
                                      :masks (mapv #(reduce bit-or 0 (keep bits (:reuse/concepts %))) entries)
                                      :eligible (atom {})}]))))))

(defn admits
  "A predicate on a step's terms (holes allowed) for a search over `index`: each theorem constant
  in them is an index entry eligible under `policy` (so a hold-out applies), each axiom an allowed
  one. Constants of `seed` (a proposal's partial proof: the caller's own choice) pass."
  [index environment policy seed]
  (let [policy (merge default-policy policy) by-id (:by-id (index-view index))
        ids #(keep (fn [x] (when (and (vector? x) (= :const (first x))) (second x))) (tree-seq vector? seq %))
        ok? (memoize #(case (:rainbow/kind (environment/declaration environment %))
                        :theorem (boolean (some-> (by-id %) (eligible? policy)))
                        :axiom (contains? (:allowed-axioms policy) %) true))
        seeded (set (ids seed))]
    (fn [value] (every? #(or (seeded %) (ok? %)) (ids value)))))

(defn query
  "Returns exact normalized-type matches in deterministic semantic order.

  Ranking exposes separate evidence components rather than an opaque score.
  Every returned `:reuse/term` still requires tactic and kernel checking."
  ([index checked-environment target] (query index checked-environment target {}))
  ([index checked-environment target policy]
   (let [policy (merge default-policy policy)
         environment-id (environment-id checked-environment)]
     (if-not (= environment-id (:reuse/environment-id index))
       {:status :rejected
        :error/category :reuse/environment-mismatch
        :expected (:reuse/environment-id index)
        :actual environment-id
        :candidates []}
       (let [target-universes (ordered-level-parameters target)
             type-key (proof/memoized ::type-key checked-environment [target target-universes]
                                      #(normalized-type-key checked-environment target target-universes
                                                            {:incremental? true :normal (fn [] (proof/normal checked-environment target))}))
             entries-by-id (:by-id (index-view index))
             target-dependencies (term/constants target)
             candidates
             (->> (get-in index [:reuse/by-type type-key] [])
                  (map entries-by-id)
                  (filter #(eligible? % policy))
                  (filter #(= (count (:reuse/type-universes %))
                              (count target-universes)))
                  (map (fn [entry]
                         (let [score {:exact-normalized-type 1
                                      :concept-overlap
                                      (count (set/intersection
                                              (:required-concepts policy)
                                              (:reuse/concepts entry)))
                                      :dependency-overlap
                                      (count (set/intersection target-dependencies
                                                               (:reuse/dependencies entry)))
                                      :successful-uses
                                      (get-in entry [:reuse/evidence :successful-uses] 0)
                                      :failed-uses
                                      (get-in entry [:reuse/evidence :failed-uses] 0)}]
                           {:reuse/declaration-id (:reuse/declaration-id entry)
                            :reuse/term (reuse-term entry target-universes)
                            :reuse/score score
                            :reuse/concepts (:reuse/concepts entry)
                            :reuse/dependencies (:reuse/dependencies entry)
                            :reuse/axioms (:reuse/axioms entry)
                            :reuse/source (:reuse/source entry)})))
                  (sort-by (fn [candidate]
                             (let [score (:reuse/score candidate)]
                               [(- (:exact-normalized-type score))
                                (- (:concept-overlap score))
                                (- (:dependency-overlap score))
                                (- (:successful-uses score))
                                (:failed-uses score)
                                (:reuse/declaration-id candidate)])))
                  vec)]
         {:status :matched
          :reuse/type-key type-key
          :candidates candidates
          :examined (count (get-in index [:reuse/by-type type-key] []))
         :returned (count candidates)})))))

(defn query-related
  "Ranks checked theorem constants as bounded global application seeds.

  This does not assert that a theorem proves the target. It retrieves only
  policy-eligible declarations sharing type-shape or constant dependencies;
  prefix synthesis and the kernel remain responsible for every application."
  ([index checked-environment target]
   (query-related index checked-environment target {}))
  ([index checked-environment target {:keys [limit] :as options}]
   (let [policy (merge default-policy (dissoc options :limit))
         environment-id (environment-id checked-environment)]
     (if-not (= environment-id (:reuse/environment-id index))
       {:status :rejected
        :error/category :reuse/environment-mismatch
        :expected (:reuse/environment-id index)
        :actual environment-id
        :candidates []}
       (let [target-levels (term-level-params target)
             target-dependencies (term/constants target)
             {:keys [bits masks eligible]} (index-view index)
             entries (:reuse/entries index)
             ;; a target's concepts are shapes, so its overlap with an entry is a count of shared shape bits
             target-mask (reduce bit-or 0 (keep bits (shape-concepts target)))
             positions (or (get @eligible [policy target-levels])
                           (let [found (filterv #(and (eligible? (entries %) policy) (reusable-in-target? (entries %) target-levels))
                                                (range (count entries)))]
                             (swap! eligible #(assoc (if (< (count %) 64) % {}) [policy target-levels] found))
                             found))
             candidates
             (->> positions
                  (keep (fn [position]
                          (let [entry (entries position)
                                score {:concept-overlap (Long/bitCount (bit-and target-mask (masks position)))
                                       :dependency-overlap (count (set/intersection target-dependencies
                                                                                    (:reuse/dependencies entry)))
                                       :successful-uses (get-in entry [:reuse/evidence :successful-uses] 0)
                                       :failed-uses (get-in entry [:reuse/evidence :failed-uses] 0)}]
                            (when (or (pos? (:dependency-overlap score)) (>= (:concept-overlap score) 3))
                              [score entry]))))
                  (sort-by (fn [[score entry]]
                             [(- (:dependency-overlap score)) (- (:concept-overlap score))
                              (- (:successful-uses score)) (:failed-uses score) (:reuse/declaration-id entry)]))
                  (take (or limit 16))
                  (mapv (fn [[score entry]]
                          {:reuse/declaration-id (:reuse/declaration-id entry)
                           :reuse/term (reuse-term entry)
                           :reuse/score score
                           :reuse/axioms (:reuse/axioms entry)
                           :reuse/source (:reuse/source entry)})))]
         {:status :matched
          :candidates candidates
          :examined (count (:reuse/entries index))
          :returned (count candidates)})))))
