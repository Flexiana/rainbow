(ns rainbow.foreign.mathlib
  "Streaming proof-redacted Mathlib catalog and coverage accounting."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [rainbow.canonical :as canonical])
  (:import (java.io BufferedInputStream FileInputStream InputStream)
           (java.security DigestInputStream MessageDigest)
           (java.util.zip GZIPInputStream)))

(def pinned-version "v4.30.0")
(def pinned-commit "c5ea00351c28e24afc9f0f84379aa41082b1188f")
(def pinned-distinct-theorem-count 424719)

(defn- bytes->hex [bytes]
  (apply str (map #(format "%02x" (bit-and 0xff %)) bytes)))

(defn- ^InputStream input-stream [path]
  (let [input (BufferedInputStream. (FileInputStream. (str path)))]
    (if (.endsWith (str path) ".gz")
      (GZIPInputStream. input 65536)
      input)))

(defn file-sha256 [path]
  (let [digest (MessageDigest/getInstance "SHA-256")
        buffer (byte-array 65536)]
    (with-open [^InputStream input (input-stream path)]
      (loop []
        (let [read-count (.read input buffer)]
          (when (pos? read-count)
            (.update digest buffer 0 read-count)
            (recur)))))
    (str "sha256:" (bytes->hex (.digest digest)))))

(defn- walk-type [form]
  ;; An iterative walk avoids consuming the JVM stack on deeply elaborated
  ;; Mathlib statements. Only vectors can be expression or universe nodes.
  (loop [pending (list form)
         profile {:operators #{} :constants #{} :unsupported #{}
                  :unsupported-features #{} :binders #{}}]
    (if-let [node (first pending)]
      (if (vector? node)
        (let [operator (first node)
              feature (when (contains? #{:unsupported :unsupported-level} operator)
                        (second node))]
          (recur
           (into (next pending) (filter vector? (rest node)))
           (cond-> profile
             (keyword? operator) (update :operators conj operator)
             (and (= :const operator) (string? (second node)))
             (update :constants conj (second node))
             feature (update :unsupported conj operator)
             (keyword? feature) (update :unsupported-features conj feature)
             (contains? #{:lam :pi} operator)
             (update :binders conj (nth node 3 nil)))))
        (recur (next pending) profile))
      profile)))

(defn type-profile [type]
  (if (map? type)
    (let [features (cond-> #{}
                     (:literal? type) (conj :literal)
                     (:metavariable? type) (conj :mvar)
                     (:free-variable? type) (conj :fvar)
                     (:projection? type) (conj :projection)
                     (:level-metavariable? type) (conj :level-mvar))
          binders (cond-> #{}
                    (:strict-implicit? type) (conj :strict-implicit)
                    (:instance-implicit? type) (conj :instance-implicit))]
      {:operators #{}
       :constants #{}
       :unsupported (if (empty? features) #{} #{:unsupported})
       :unsupported-features features
       :binders binders
       :unsupported-operators (if (empty? features) #{} #{:unsupported})
       :unsupported-binders binders
       :rainbow-structural-fragment? (and (empty? features) (empty? binders))})
    (let [profile (walk-type type)
          supported-operators #{:sort :zero :succ :max :imax :param :bound
                                :const :app :lam :pi :let}
          unsupported-operators (remove supported-operators (:operators profile))
          unsupported-binders (remove #{:explicit :implicit} (:binders profile))]
      (assoc profile
             :rainbow-structural-fragment?
             (and (empty? (:unsupported profile))
                  (empty? unsupported-operators)
                  (empty? unsupported-binders))
             :unsupported-operators (set unsupported-operators)
             :unsupported-binders (set unsupported-binders)))))

(defn statement-constant-names
  "Returns the exact foreign constants referenced by one bounded statement.

  Compact catalog profiles intentionally omit this dependency data; it becomes
  available after the proof-redacted full type is selected and exported."
  [statement]
  (:constants (type-profile (:foreign/type statement))))

(defn audit-statement-dependencies
  "Ranks a bounded statement batch by whether all foreign constants have an
  explicit nativeization. This is a syntactic readiness signal, not a claim
  that the theorem is constructively derivable."
  [statements nativeized-foreign-constants]
  (let [nativeized (set nativeized-foreign-constants)
        audited
        (mapv (fn [statement]
                (let [constants (statement-constant-names statement)
                      unresolved (remove nativeized constants)]
                  {:foreign/name (:foreign/name statement)
                   :foreign/constants (vec (sort constants))
                   :unresolved (vec (sort unresolved))
                   :fully-nativeizable? (empty? unresolved)}))
              statements)
        unresolved-counts
        (into (sorted-map)
              (frequencies (mapcat :unresolved audited)))]
    {:statement-count (count audited)
     :fully-nativeizable (count (filter :fully-nativeizable? audited))
     :with-unresolved (count (remove :fully-nativeizable? audited))
     :unresolved-constant-counts unresolved-counts
     :statements audited}))

(defn reduce-catalog
  "Streams an ND-EDN catalog. `step` receives the accumulator and each
  declaration; the proof-redacted catalog need not fit in memory."
  [path initial step]
  (let [digest (MessageDigest/getInstance "SHA-256")]
    (with-open [reader (clojure.java.io/reader
                        (DigestInputStream. (input-stream path) digest))]
      (let [lines (line-seq reader)
            header (edn/read-string (first lines))]
        (when-not (and (= :header (:rainbow.catalog/kind header))
                       (= :mathlib (:foreign/library header))
                       (= pinned-version (:foreign/version header))
                       (= pinned-commit (:foreign/commit header))
                       (= :redacted (:foreign/proofs header))
                       (= :lean-hash64-profile
                          (:foreign/statement-representation header))
                       (= 2 (:foreign/schema-version header)))
          (throw (ex-info
                  "Catalog header does not match pinned proof-redacted Mathlib"
                  {:error/category :mathlib/catalog-header
                   :header header})))
        (let [result
              (reduce (fn [accumulator line]
                        (let [declaration (edn/read-string line)]
                          (when-not (and (= :declaration
                                            (:rainbow.catalog/kind declaration))
                                         (= :redacted (:foreign/value declaration))
                                         (string? (:foreign/type-fingerprint declaration))
                                         (map? (:foreign/type-profile declaration))
                                         (boolean? (:foreign/public? declaration))
                                         (pos-int? (get-in declaration
                                                           [:foreign/type-profile :nodes])))
                            (throw (ex-info
                                    "Catalog declaration is not proof-redacted"
                                    {:error/category :mathlib/catalog-declaration
                                     :declaration declaration})))
                          (step accumulator declaration)))
                      initial (next lines))]
          {:header header
           :catalog/id (str "sha256:" (bytes->hex (.digest digest)))
           :result result})))))

(defn summarize [path proved-foreign-names]
  (let [{:keys [header result catalog/id]}
        (reduce-catalog
         path
         {:declarations 0 :theorems 0 :proved 0 :unsafe 0
          :public-theorems 0 :private-theorems 0
          :theorem-names #{} :public-theorem-names #{}
          :structural-theorem-names #{} :proved-theorem-names #{}
          :kinds {} :modules #{} :structural-fragment-theorems 0
          :unsupported-binders {} :unsupported-operators {}
          :unsupported-features {} :constant-theorem-counts {}
          :theorem-module-counts {} :candidate-theorems []}
         (fn [summary declaration]
           (let [theorem? (= :theorem (:foreign/kind declaration))
                 profile (when theorem?
                           (type-profile (or (:foreign/type-profile declaration)
                                             (:foreign/type declaration))))]
             (cond-> (-> summary
                         (update :declarations inc)
                         (update-in [:kinds (:foreign/kind declaration)] (fnil inc 0))
                         (update :modules conj (:foreign/module declaration))
                         (cond-> (:foreign/unsafe? declaration) (update :unsafe inc)))
               theorem? (update :theorems inc)
               theorem? (update :theorem-names conj (:foreign/name declaration))
               (and theorem? (:foreign/public? declaration))
               (update :public-theorem-names conj (:foreign/name declaration))
               (and theorem? (:foreign/public? declaration))
               (update :public-theorems inc)
               (and theorem? (false? (:foreign/public? declaration)))
               (update :private-theorems inc)
               theorem?
               (update-in [:theorem-module-counts (:foreign/module declaration)]
                          (fnil inc 0))
               (and theorem? (contains? proved-foreign-names
                                        (:foreign/name declaration)))
               (update :proved inc)
               (and theorem? (contains? proved-foreign-names
                                        (:foreign/name declaration)))
               (update :proved-theorem-names conj (:foreign/name declaration))
               (and theorem? (:rainbow-structural-fragment? profile))
               (update :structural-fragment-theorems inc)
               (and theorem? (:rainbow-structural-fragment? profile))
               (update :structural-theorem-names conj (:foreign/name declaration))
               (and theorem? (:foreign/public? declaration)
                    (:rainbow-structural-fragment? profile)
                    (not (contains? proved-foreign-names
                                    (:foreign/name declaration))))
               (update :candidate-theorems
                       (fn [candidates]
                         (->> (conj candidates
                                    {:foreign/name (:foreign/name declaration)
                                     :foreign/module (:foreign/module declaration)
                                     :foreign/type-fingerprint
                                     (:foreign/type-fingerprint declaration)
                                     :foreign/type-nodes
                                     (get-in declaration [:foreign/type-profile :nodes])})
                              (sort-by (juxt :foreign/type-nodes
                                             :foreign/module :foreign/name))
                              (take 16)
                              vec)))
               theorem?
               (update :unsupported-binders
                       #(merge-with + % (frequencies (:unsupported-binders profile))))
               theorem?
               (update :unsupported-operators
                       #(merge-with + % (frequencies (:unsupported-operators profile))))
               theorem?
               (update :unsupported-features
                       #(merge-with + %
                                    (frequencies (:unsupported-features profile))))
               theorem?
               (update :constant-theorem-counts
                       #(merge-with + % (frequencies (:constants profile))))))))]
    (let [theorem-names (:theorem-names result)
          public-names (:public-theorem-names result)
          summary (-> result
                      (update :modules count)
                      (assoc :declaration-occurrences (:declarations result)
                             :theorem-occurrences (:theorems result)
                             :theorems (count theorem-names)
                             :public-theorems (count public-names)
                             :private-theorems
                             (count (set/difference theorem-names public-names))
                             :proved (count (:proved-theorem-names result))
                             :structural-fragment-theorems
                             (count (:structural-theorem-names result))
                             :catalog/id id
                             :foreign/version (:foreign/version header)
                             :foreign/commit (:foreign/commit header)
                             :proofs-redacted? true)
                      (dissoc :theorem-names :public-theorem-names
                              :proved-theorem-names
                              :structural-theorem-names))]
      (assoc summary :coverage
             {:proved (:proved summary)
              :total (:theorems summary)
              :ratio (if (pos? (:theorems summary))
                       (/ (:proved summary) (:theorems summary)) 0)}))))

(defn declaration-id [declaration]
  (canonical/content-id
   (select-keys declaration [:foreign/name :foreign/kind :foreign/module
                             :foreign/universes :foreign/type-fingerprint
                             :foreign/unsafe? :foreign/public?])))

(defn select-declarations [catalog-path foreign-names]
  (let [wanted (set foreign-names)
        {:keys [result] :as reduced}
        (reduce-catalog
         catalog-path {}
         (fn [selected declaration]
           (if (contains? wanted (:foreign/name declaration))
             (assoc selected (:foreign/name declaration) declaration)
             selected)))]
    (when-not (= wanted (set (keys result)))
      (throw (ex-info "Some requested declarations are absent from the catalog"
                      {:error/category :mathlib/catalog-selection
                       :requested wanted :found (set (keys result))})))
    (assoc reduced :result result)))

(def default-study-module-prefixes
  ["Mathlib.Logic"])

(defn- module-selected? [prefixes module]
  (some #(or (= % module) (.startsWith ^String module (str % "."))) prefixes))

(defn select-study-curriculum
  "Selects a deterministic, proof-redacted proving curriculum from the compact
  catalog. Selection uses declaration metadata only; Lean proof values and
  source theorem bodies are never read. The returned split is stable for the
  pinned catalog and independent of catalog line order."
  ([catalog-path] (select-study-curriculum catalog-path {}))
  ([catalog-path {:keys [target-count exclude-foreign-names module-prefixes
                         maximum-type-nodes]
                  :or {target-count 1024 exclude-foreign-names #{}
                       module-prefixes default-study-module-prefixes
                       maximum-type-nodes 256}}]
   (when-not (and (pos-int? target-count) (pos-int? maximum-type-nodes)
                  (sequential? module-prefixes) (seq module-prefixes)
                  (every? string? module-prefixes))
     (throw (ex-info "Invalid Mathlib study curriculum options"
                     {:error/category :mathlib/invalid-study-options})))
   (let [excluded (set exclude-foreign-names)
         {:keys [header catalog/id result]}
         (reduce-catalog
          catalog-path []
          (fn [candidates declaration]
            (let [profile (:foreign/type-profile declaration)]
              (if (and (= :theorem (:foreign/kind declaration))
                       (:foreign/public? declaration)
                       (not (:foreign/unsafe? declaration))
                       (not (contains? excluded (:foreign/name declaration)))
                       (module-selected? module-prefixes
                                         (:foreign/module declaration))
                       (<= (get profile :nodes Long/MAX_VALUE)
                           maximum-type-nodes)
                       (:rainbow-structural-fragment? (type-profile profile)))
                (conj candidates
                      (select-keys declaration
                                   [:foreign/name :foreign/module
                                    :foreign/type-fingerprint
                                    :foreign/type-profile]))
                candidates))))
         ordered
         (->> (sort-by (juxt #(get-in % [:foreign/type-profile :nodes])
                             :foreign/module :foreign/name
                             :foreign/type-fingerprint)
                       result)
              (reduce (fn [{:keys [seen declarations] :as state} declaration]
                        (let [foreign-name (:foreign/name declaration)]
                          (if (contains? seen foreign-name)
                            state
                            {:seen (conj seen foreign-name)
                             :declarations (conj declarations declaration)})))
                      {:seen #{} :declarations []})
              :declarations
              (take target-count)
              vec)
         targets (mapv (fn [index declaration]
                         (assoc declaration :study/partition
                                (cond
                                  (= 8 (mod index 10)) :held-out
                                  (= 9 (mod index 10)) :transfer
                                  :else :development)))
                       (range) ordered)
         base {:study/schema-version 1
               :study/source {:foreign/library :mathlib
                              :foreign/version (:foreign/version header)
                              :foreign/commit (:foreign/commit header)
                              :catalog/id id
                              :proof-values :redacted}
               :study/selection {:requested target-count
                                 :selected (count targets)
                                 :maximum-type-nodes maximum-type-nodes
                                 :module-prefixes (vec module-prefixes)
                                 :excluded (count excluded)}
               :study/partition-counts (frequencies (map :study/partition targets))
               :study/targets targets}]
     (assoc base :study/id (canonical/content-id base)))))

(defn load-statement-batch [path expected-foreign-names]
  (with-open [reader (clojure.java.io/reader path)]
    (let [forms (mapv edn/read-string (line-seq reader))
          header (first forms)
          statements (next forms)
          expected (set expected-foreign-names)
          actual (set (map :foreign/name statements))]
      (when-not (and (= :header (:rainbow.catalog/kind header))
                     (= :mathlib (:foreign/library header))
                     (= pinned-version (:foreign/version header))
                     (= pinned-commit (:foreign/commit header))
                     (= :redacted (:foreign/proofs header))
                     (= :bounded (:foreign/selection header))
                     (= 1 (:foreign/schema-version header))
                     (= expected actual)
                     (= (count expected) (count statements))
                     (every? #(and (= :statement (:rainbow.catalog/kind %))
                                   (= :redacted (:foreign/value %))
                                   (string? (:foreign/type-fingerprint %))
                                   (or (nil? (:foreign/universes %))
                                       (and (vector? (:foreign/universes %))
                                            (every? string?
                                                    (:foreign/universes %))))
                                   (vector? (:foreign/type %)))
                             statements))
        (throw (ex-info "Invalid or mismatched proof-redacted statement batch"
                        {:error/category :mathlib/statement-batch
                         :header header :expected expected :actual actual})))
      {:header header
       :batch/id (file-sha256 path)
       :statements (vec statements)})))

(defn verify-statement-batch [catalog-path statement-path foreign-names]
  (let [{catalog-id :catalog/id declarations :result}
        (select-declarations catalog-path foreign-names)
        batch (load-statement-batch statement-path foreign-names)
        fingerprints (into {} (map (juxt :foreign/name :foreign/type-fingerprint)
                                   (:statements batch)))
        expected-fingerprints
        (into {} (map (fn [[name declaration]]
                        [name (:foreign/type-fingerprint declaration)]))
              declarations)]
    (when-not (= expected-fingerprints fingerprints)
      (throw (ex-info "Statement batch differs from the coverage catalog"
                      {:error/category :mathlib/statement-fingerprint
                       :catalog expected-fingerprints :batch fingerprints})))
    (assoc batch :status :verified :catalog/id catalog-id)))
