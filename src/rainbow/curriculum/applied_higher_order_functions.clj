(ns rainbow.curriculum.applied-higher-order-functions
  "Traceable proof-or-bug ledger for the sibling AHoF book catalog."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]))

(def schema-version 1)
(def default-source-root "../ahof")
(def ledger-path "artifacts/or40/ahof-algorithm-ledger.edn")
(def source-commit "0f53d3bc40bbe2e110f3fda4325d205322cce53c")

(def domain-specs
  [{:domain :optimization
    :prefix "O"
    :expected-count 75
    :path "catalog/01_optimization_algorithms.md"}
   {:domain :decision-making
    :prefix "D"
    :expected-count 83
    :path "catalog/02_decision_making_algorithms.md"}
   {:domain :validation
    :prefix "V"
    :expected-count 64
    :path "catalog/03_validation_algorithms.md"}])

(defn- pattern-keyword [value]
  (-> value
      string/trim
      string/lower-case
      (string/replace #"[^a-z0-9]+" "-")
      (string/replace #"(^-|-$)" "")
      keyword))

(defn- patterns [primary secondary]
  (->> [primary secondary]
       (mapcat #(string/split % #"\s*\+\s*"))
       (map string/trim)
       (remove #{"" "—" "-"})
       (map pattern-keyword)
       distinct
       vec))

(defn- catalog-row [domain source-file category line]
  (let [cells (mapv string/trim (string/split line #"\|" -1))
        [_ id name primary secondary] cells]
    (when (and id (re-matches #"[ODV][0-9]+" id))
      {:ahof/id id
       :ahof/domain domain
       :ahof/name name
       :ahof/category category
       :ahof/patterns (patterns primary secondary)
       :ahof/source-file source-file
       :ahof/outcome :pending
       :ahof/pending-reason :not-yet-audited
       :ahof/evidence []})))

(defn parse-catalog-text
  "Parses the stable ID, name, category, and HOF patterns from one catalog."
  [domain source-file text]
  (:algorithms
   (reduce
    (fn [{:keys [category] :as state} line]
      (if-let [[_ heading] (re-matches #"###\s+(.+)" line)]
        (assoc state :category heading)
        (if-let [row (catalog-row domain source-file category line)]
          (update state :algorithms conj row)
          state)))
    {:category nil :algorithms []}
    (string/split-lines text))))

(defn- source-file [source-root relative-path]
  (io/file source-root relative-path))

(defn- read-domain [source-root spec]
  (let [file (source-file source-root (:path spec))
        text (slurp file)
        algorithms (parse-catalog-text (:domain spec) (:path spec) text)]
    (when-not (= (:expected-count spec) (count algorithms))
      (throw (ex-info "AHoF catalog count changed"
                      {:domain (:domain spec)
                       :expected (:expected-count spec)
                       :actual (count algorithms)
                       :path (str file)})))
    {:source
     {:path (:path spec)
      :content-sha256 (canonical/sha256 text)
      :algorithm-count (count algorithms)}
     :algorithms algorithms}))

(defn- dependency-cone [{:ahof/keys [name patterns]}]
  (let [label (string/lower-case name)
        pattern-set (set patterns)]
    (cond
      (re-find #"particle swarm|genetic|evolution|population|firefly|cuckoo|cma-es"
               label)
      :population-evolution

      (re-find #"bellman|value iteration|policy iteration|policy evaluation|mdp"
               label)
      :bellman-and-fixed-points

      (re-find #"mcmc|metropolis|gibbs|hamiltonian|sampling|monte carlo|particle filter|importance"
               label)
      :sampling-and-markov-kernels

      (or (contains? pattern-set :transform-problem)
          (re-find #"falsification|robust|constraint|reachability" label))
      :problem-transformers

      (or (contains? pattern-set :branch)
          (re-find #"search|tree|graph|simplex|branch and bound" label))
      :exploration-and-discrete-optimization

      :else :generic-exact-foundations)))

(defn build-ledger
  ([source-root]
   (build-ledger source-root {:commit source-commit
                              :working-tree-dirty? true}))
  ([source-root {:keys [commit working-tree-dirty?]}]
   (let [domains (mapv #(read-domain source-root %) domain-specs)
         algorithms
         (->> domains
              (mapcat :algorithms)
              (mapv #(assoc % :ahof/dependency-cone (dependency-cone %))))
         ids (mapv :ahof/id algorithms)
         base
         {:ahof-ledger/schema-version schema-version
          :ahof-ledger/window
          {:start "2026-08-18" :conference "2026-09-27" :days 40}
          :ahof-ledger/source
          {:repository "../ahof"
           :commit commit
           :working-tree-dirty? (boolean working-tree-dirty?)
           :catalog-files (mapv :source domains)}
          :ahof-ledger/scope
          {:authoritative :detailed-catalog
           :algorithms 222
           :domain-counts {:optimization 75
                           :decision-making 83
                           :validation 64}
           :master-catalog-claim 406
           :count-discrepancy :explicit-unresolved-source-scope}
          :ahof-ledger/acceptance
          {:terminal-outcomes #{:proved :bug}
           :proof-requires
           [:precise-specification :kernel-checked-proof :axiom-profile
            :checked-specialization-when-reused]
           :bug-requires
           [:exact-source-location :minimal-reproduction :expected-claim
            :observed-counterexample-or-failure]
           :executable-claim-boundaries
           [:mathematical-theorem :rainbow-evaluation
            :clojure-correspondence :output-satisfies-theorem]}
          :ahof-ledger/summary
          {:total (count algorithms)
           :unique-ids (count (distinct ids))
           :outcomes {:pending (count algorithms) :proved 0 :bug 0}
           :credited-results {:total 0 :outcomes {}}
           :dependency-cones
           (into (sorted-map) (frequencies (map :ahof/dependency-cone
                                                algorithms)))}
          :ahof-ledger/algorithms algorithms}]
     (when-not (= (count ids) (count (distinct ids)))
       (throw (ex-info "AHoF catalog IDs are not unique" {:ids ids})))
     (assoc base :ahof-ledger/id (canonical/content-id base)))))

(defn credit-result
  "Adds or replaces a content-addressed proved/bug result without pretending
  that a supplemental result is one of the 222 catalog rows."
  [ledger entry]
  (when-not (contains? #{:proved :bug} (:ahof/outcome entry))
    (throw (ex-info "AHoF credit must be terminal"
                    {:entry entry})))
  (when-not (and (string? (:ahof/id entry))
                 (seq (:ahof/evidence entry)))
    (throw (ex-info "AHoF credit requires identity and evidence"
                    {:entry entry})))
  (let [entries
        (->> (conj (vec (remove #(= (:ahof/id entry) (:ahof/id %))
                                (:ahof-ledger/credited-results ledger)))
                   entry)
             (sort-by :ahof/id)
             vec)
        outcomes (frequencies (map :ahof/outcome entries))
        base
        (-> ledger
            (dissoc :ahof-ledger/id)
            (assoc :ahof-ledger/credited-results entries)
            (assoc-in [:ahof-ledger/summary :credited-results]
                      {:total (count entries)
                       :outcomes (into (sorted-map) outcomes)}))]
    (assoc base :ahof-ledger/id (canonical/content-id base))))

(defn credit-catalog-result
  "Credits one of the 222 stable catalog rows and recomputes catalog outcomes.
  Shared prerequisites stay in evidence and are not counted as algorithms."
  [ledger entry]
  (when-not (contains? #{:proved :bug} (:ahof/outcome entry))
    (throw (ex-info "AHoF catalog credit must be terminal" {:entry entry})))
  (when-not (and (string? (:ahof/id entry))
                 (seq (:ahof/evidence entry)))
    (throw (ex-info "AHoF catalog credit requires identity and evidence"
                    {:entry entry})))
  (let [matches (filterv #(= (:ahof/id entry) (:ahof/id %))
                         (:ahof-ledger/algorithms ledger))]
    (when-not (= 1 (count matches))
      (throw (ex-info "AHoF catalog credit must resolve one stable row"
                      {:id (:ahof/id entry) :matches (count matches)})))
    (let [algorithms
          (mapv
           (fn [algorithm]
             (if (= (:ahof/id entry) (:ahof/id algorithm))
               (-> algorithm
                   (merge (dissoc entry :ahof/domain :ahof/name))
                   (dissoc :ahof/pending-reason))
               algorithm))
           (:ahof-ledger/algorithms ledger))
          outcomes (merge {:pending 0 :proved 0 :bug 0}
                          (frequencies (map :ahof/outcome algorithms)))
          base
          (-> ledger
              (dissoc :ahof-ledger/id)
              (assoc :ahof-ledger/algorithms algorithms)
              (assoc-in [:ahof-ledger/summary :outcomes] outcomes))]
      (assoc base :ahof-ledger/id (canonical/content-id base)))))

(defn write-credited-ledger! [path ledger]
  (io/make-parents path)
  (spit path (str (pr-str ledger) "\n"))
  ledger)

(defn write-ledger!
  ([] (write-ledger! default-source-root ledger-path))
  ([source-root path]
   (let [value (build-ledger source-root)]
     (io/make-parents path)
     (spit path (str (pr-str value) "\n"))
     value)))

(defn load-ledger [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :ahof-ledger/id))]
      (if (and (= expected (:ahof-ledger/id value))
               (= 222 (count (:ahof-ledger/algorithms value))))
        {:status :replayed :ledger value}
        {:status :rejected
         :error/category :ahof-ledger/identity-or-count-mismatch
         :expected expected
         :actual (:ahof-ledger/id value)}))
    (catch Throwable throwable
      {:status :rejected
       :error/category :ahof-ledger/read-failed
       :message (.getMessage throwable)})))
