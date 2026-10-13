(ns rainbow.curriculum.operations-research
  "Proof-redacted, prerequisite-ordered operations-research curriculum.

  Topic selection is planning data, not proof evidence. Exact foreign coverage
  is credited only when a selected global Mathlib name has a kernel-checked
  Rainbow mapping in the cumulative checkpoint."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as string]
            [rainbow.algebra.finite :as finite]
            [rainbow.canonical :as canonical]
            [rainbow.foreign.ingest :as ingest]
            [rainbow.checkpoint :as day54]
            [rainbow.foreign.aliases.finite-sets :as finite-sets]
            [rainbow.search.preset-wide :as preset-wide]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.kernel :as kernel])
  (:import (java.time LocalDate)))

(def schema-version 1)
(def start-date "2026-08-18")
(def conference-date "2026-09-27")
(def report-path "artifacts/or40/report.edn")
(def curriculum-path "artifacts/or40/curriculum.edn")
(def default-catalog-path preset-wide/default-catalog-path)
(def default-checkpoint-path preset-wide/checkpoint-path)
(def default-request-path "/tmp/rainbow-or40-foundation-requests.tsv")
(def default-statement-path "/tmp/rainbow-or40-foundation-statements.edn")
(def maximum-type-nodes 512)

(def phase-specs
  [{:phase/id :common-foundations
    :days [1 7]
    :target-count 1200
    :requires []
    :module-prefixes
    ["Mathlib.Data.Set.Finite" "Mathlib.Data.Finset" "Mathlib.Data.Fintype"
     "Mathlib.Algebra.BigOperators" "Mathlib.Algebra.Order.BigOperators"]
    :exit-criteria
    [:exact-finite-sums :finite-expectation-laws :order-and-norm-basics
     :finite-matrices :checked-runnable-reference-semantics]}
   {:phase/id :bellman-operators
    :days [8 15]
    :target-count 1000
    :requires [:common-foundations]
    :module-prefixes
    ["Mathlib.Order" "Mathlib.Dynamics.FixedPoints"
     "Mathlib.Topology.MetricSpace.Contracting"]
    :exit-criteria
    [:bellman-monotone :bellman-gamma-contraction
     :unique-bellman-fixed-point :value-iteration-error-bound
     :bellman-residual-error-bound :finite-mdp-demo]}
   {:phase/id :mcmc
    :days [16 26]
    :target-count 500
    :requires [:common-foundations]
    :module-prefixes
    ["Mathlib.Probability.ProbabilityMassFunction"
     "Mathlib.Probability.Kernel" "Mathlib.Probability.Martingale"
     "Mathlib.Dynamics.Ergodic"]
    :exit-criteria
    [:pmf-normalization :kernel-composition :detailed-balance-stationary
     :invariant-measure :ergodic-average :metropolis-hastings-demo]}
   {:phase/id :bird-flock-optimization
    :days [27 34]
    :target-count 2000
    :requires [:common-foundations]
    :module-prefixes
    ["Mathlib.Analysis.Convex" "Mathlib.Analysis.InnerProductSpace"
     "Mathlib.LinearAlgebra.FiniteDimensional"
     "Mathlib.Analysis.Normed.Module.FiniteDimension"]
    :exit-criteria
    [:vector-update-semantics :best-so-far-monotone
     :convex-combination-bounds :bounded-trajectory-under-assumptions
     :stochastic-claim-boundaries :particle-swarm-demo]}
   {:phase/id :conference-integration
    :days [35 40]
    :target-count 300
    :requires [:bellman-operators :mcmc :bird-flock-optimization]
    :module-prefixes
    ["Mathlib.Probability.Decision.Risk"
     "Mathlib.Combinatorics.Optimization"
     "Mathlib.Probability.Distributions" "Mathlib.Probability.Moments"]
    :exit-criteria
    [:cross-track-example :compiled-reference-agreement
     :prover-soundness-regression-suite :reproducible-conference-demo] }])

(defn- module-selected? [prefixes module]
  (some #(or (= % module) (.startsWith ^String module (str % "."))) prefixes))

(defn- eligible? [declaration]
  (let [profile (:foreign/type-profile declaration)]
    (and (= :theorem (:foreign/kind declaration))
         (:foreign/public? declaration)
         (not (:foreign/unsafe? declaration))
         (<= (get profile :nodes Long/MAX_VALUE) maximum-type-nodes))))

(defn- declaration-phase [specs declaration]
  (some #(when (module-selected? (:module-prefixes %)
                                 (:foreign/module declaration))
           (:phase/id %))
        specs))

(defn- target-order [target]
  [(get-in target [:foreign/type-profile :nodes])
   (:foreign/module target) (:foreign/name target)
   (:foreign/type-fingerprint target)])

(defn- distinct-declarations [declarations]
  (:declarations
   (reduce (fn [{:keys [seen] :as state} declaration]
             (let [name (:foreign/name declaration)]
               (if (contains? seen name)
                 state
                 (-> state
                     (update :seen conj name)
                     (update :declarations conj declaration)))))
           {:seen #{} :declarations []}
           declarations)))

(defn- partition-targets [phase-id declarations]
  (mapv (fn [index declaration]
          (assoc declaration
                 :or/phase phase-id
                 :study/partition (cond
                                    (= 8 (mod index 10)) :held-out
                                    (= 9 (mod index 10)) :transfer
                                    :else :development)))
        (range) declarations))

(defn select-curriculum
  "Selects a deterministic 5,000-statement OR corpus from catalog metadata.
  Lean proof values and source theorem bodies are never read."
  ([catalog-path] (select-curriculum catalog-path phase-specs))
  ([catalog-path specs]
   (let [phase-ids (mapv :phase/id specs)
         {:keys [header catalog/id result]}
         (mathlib/reduce-catalog
          catalog-path (zipmap phase-ids (repeat []))
          (fn [selected declaration]
            (if-let [phase-id (and (eligible? declaration)
                                   (declaration-phase specs declaration))]
              (update selected phase-id conj
                      (assoc
                       (select-keys declaration
                                    [:foreign/name :foreign/module
                                     :foreign/type-fingerprint
                                     :foreign/type-profile])
                       :rainbow/structural-fragment?
                       (:rainbow-structural-fragment?
                        (mathlib/type-profile
                         (:foreign/type-profile declaration)))))
              selected)))
         phases
         (mapv
          (fn [spec]
            (let [requested (:target-count spec)
                  candidates (->> (get result (:phase/id spec))
                                  (sort-by target-order)
                                  distinct-declarations
                                  (take requested)
                                  vec)]
              (when-not (= requested (count candidates))
                (throw (ex-info "Insufficient pinned Mathlib OR candidates"
                                {:error/category :or/insufficient-candidates
                                 :phase/id (:phase/id spec)
                                 :requested requested
                                 :available (count candidates)})))
              (assoc spec :selected requested
                     :targets (partition-targets (:phase/id spec) candidates))))
          specs)
         targets (vec (mapcat :targets phases))
         names (mapv :foreign/name targets)
         expected-date (str (.plusDays (LocalDate/parse start-date) 40))
         _ (when-not (and (= conference-date expected-date)
                          (= (count names) (count (distinct names))))
             (throw (ex-info "Invalid OR schedule or duplicate target"
                             {:error/category :or/invalid-curriculum})))
         base
         {:or.curriculum/schema-version schema-version
          :or.curriculum/window {:start start-date :days 40
                                 :conference conference-date}
          :or.curriculum/source
          {:foreign/library :mathlib
           :foreign/version (:foreign/version header)
           :foreign/commit (:foreign/commit header)
           :catalog/id id :proof-values :redacted}
          :or.curriculum/selection
          {:selected (count targets) :maximum-type-nodes maximum-type-nodes
           :partition-counts (frequencies (map :study/partition targets))
           :structural-fragment-ready
           (count (filter :rainbow/structural-fragment? targets))
           :representation-work-required
           (count (remove :rainbow/structural-fragment? targets))}
          :or.curriculum/prerequisite-graph
          (into (sorted-map) (map (juxt :phase/id :requires)) phases)
          :or.curriculum/phases phases
          :or.curriculum/targets targets}]
     (assoc base :or.curriculum/id (canonical/content-id base)))))

(defn audit-coverage [curriculum mappings]
  (let [mapped (set (map :foreign/name mappings))
        selected (set (map :foreign/name (:or.curriculum/targets curriculum)))
        exact (set/intersection mapped selected)]
    {:selected-targets (count selected)
     :exact-selected-mappings (count exact)
     :ratio (/ (count exact) (count selected))
     :by-phase
     (into (sorted-map)
           (map (fn [{:keys [phase/id targets]}]
                  [id {:selected (count targets)
                       :exact-mappings
                       (count (filter #(contains? exact (:foreign/name %))
                                      targets))}]))
           (:or.curriculum/phases curriculum))}))

(defn next-proof-batch
  "Returns the next unmapped targets in one phase. Structural readiness can be
  required for immediate proving or disabled for representation research."
  ([curriculum mappings]
   (next-proof-batch curriculum mappings {}))
  ([curriculum mappings {:keys [phase target-count structural-only?]
                         :or {phase :common-foundations target-count 128
                              structural-only? true}}]
   (when-not (and (keyword? phase) (pos-int? target-count)
                  (boolean? structural-only?))
     (throw (ex-info "Invalid OR batch selection"
                     {:error/category :or/invalid-batch-selection})))
   (let [mapped (set (map :foreign/name mappings))
         candidates
         (->> (:or.curriculum/targets curriculum)
              (filter #(= phase (:or/phase %)))
              (remove #(contains? mapped (:foreign/name %)))
              (filter #(or (not structural-only?)
                           (:rainbow/structural-fragment? %)))
              (take target-count)
              vec)]
     (when-not (= target-count (count candidates))
       (throw (ex-info "Insufficient unmapped OR batch candidates"
                       {:error/category :or/insufficient-batch-candidates
                        :phase phase :requested target-count
                        :available (count candidates)})))
     candidates)))

(defn write-next-request!
  ([curriculum checkpoint output-path]
   (write-next-request! curriculum checkpoint output-path {}))
  ([curriculum checkpoint output-path options]
   (let [targets (next-proof-batch curriculum (:mappings checkpoint) options)
         lines (map #(str (:foreign/name %) "\t" (:foreign/module %)) targets)]
     (spit output-path (str (string/join "\n" lines) "\n"))
     {:status :written :path (str output-path) :targets (count targets)
      :request/id
      (canonical/content-id
       {:curriculum/id (:or.curriculum/id curriculum)
        :checkpoint/id (:checkpoint/id checkpoint)
        :options (merge {:phase :common-foundations :target-count 128
                         :structural-only? true} options)
        :targets (mapv :foreign/name targets)})})))

(defn audit-next-batch
  ([statement-path curriculum checkpoint]
   (audit-next-batch statement-path curriculum checkpoint {}))
  ([statement-path curriculum checkpoint options]
   (let [targets (next-proof-batch curriculum (:mappings checkpoint) options)
         names (mapv :foreign/name targets)
         batch (mathlib/verify-statement-batch default-catalog-path
                                               statement-path names)
         readiness
         (mathlib/audit-statement-dependencies
          (:statements batch) (set (keys finite-sets/constant-aliases)))
         native-results
         (mapv #(ingest/nativeize-statement
                 (:environment checkpoint) % finite-sets/constant-aliases)
               (:statements batch))
         native-statuses (frequencies (map :status native-results))
         rejection-categories
         (frequencies (keep #(get-in % [:error :error/category])
                            native-results))
         base
         {:status :audited
          :curriculum/id (:or.curriculum/id curriculum)
          :checkpoint/id (:checkpoint/id checkpoint)
          :statement-batch/id (:batch/id batch)
          :targets (count targets)
          :fully-nativeizable (:fully-nativeizable readiness)
          :with-unresolved (:with-unresolved readiness)
          :kernel-nativeized (get native-statuses :nativeized 0)
          :nativeization-rejected (get native-statuses :rejected 0)
          :nativeization-rejection-categories rejection-categories
          :top-unresolved-constants
          (->> (:unresolved-constant-counts readiness)
               (sort-by (juxt (comp - val) key))
               (take 32) vec)
          :single-blocker-statements
          (count (filter #(= 1 (count (:unresolved %)))
                         (:statements readiness)))}]
     (assoc base :audit/id (canonical/content-id base)))))

(defn build-report
  ([catalog-path checkpoint-path]
   (build-report catalog-path checkpoint-path
                 (select-curriculum catalog-path)))
  ([catalog-path checkpoint-path curriculum]
  (let [
        checkpoint (day54/load-checkpoint checkpoint-path)
        _ (when-not (= :replayed (:status checkpoint))
            (throw (ex-info "OR baseline checkpoint rejected"
                            {:error/category :or/checkpoint-rejected
                             :checkpoint checkpoint})))
        finite-build (finite/build)
        finite-results (:results finite-build)
        native-names (mapv :name finite-results)
        native-axioms
        (into (sorted-map)
              (map (fn [name]
                     [name (kernel/axioms (:environment finite-build) name)]))
              native-names)
        coverage (audit-coverage curriculum (:mappings checkpoint))
        base
        {:status :passed
         :curriculum/id (:or.curriculum/id curriculum)
         :window (:or.curriculum/window curriculum)
         :source (:or.curriculum/source curriculum)
         :curriculum
         {:selected (get-in curriculum [:or.curriculum/selection :selected])
          :partition-counts
          (get-in curriculum [:or.curriculum/selection :partition-counts])
          :structural-fragment-ready
          (get-in curriculum [:or.curriculum/selection
                              :structural-fragment-ready])
          :representation-work-required
          (get-in curriculum [:or.curriculum/selection
                              :representation-work-required])
          :phase-counts
          (into (sorted-map)
                (map (fn [{:keys [phase/id selected days]}]
                       [id {:selected selected :days days}]))
                (:or.curriculum/phases curriculum))}
         :baseline
         {:all-mathlib-exact-mappings (count (:mappings checkpoint))
          :all-mathlib-theorems mathlib/pinned-distinct-theorem-count
          :or coverage}
         :first-foundation-cluster
         {:kind :exact-finite-natural-sums
          :native-theorems (count finite-results)
          :new-conference-theorems
          ['algebra/finite-sum-zero-cons 'algebra/finite-sum-singleton]
          :theorem-names native-names
          :axiom-profiles (frequencies (vals native-axioms))
          :all-kernel-rechecked? true}
         :claim-boundaries
         {:topic-selection-is-proof-credit? false
          :native-theorems-counted-as-mathlib-mappings? false
          :foreign-proof-values-present? false
          :bellman-mcmc-and-flock-demos-complete? false
          :conference-outcome-guaranteed? false
          :trusted-kernel-change :none}}
        passed? (and (= 5000 (get-in base [:curriculum :selected]))
                     (= 11 (get-in base [:first-foundation-cluster
                                         :native-theorems]))
                     (every? empty? (vals native-axioms)))]
    (assoc base :status (if passed? :passed :failed)
           :report/id (canonical/content-id (assoc base :status
                                                    (if passed? :passed :failed)))))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :or/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :or/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-edn! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command first-path second-path third-path fourth-argument]]
  (case command
    "replay"
    (let [result (load-report (or first-path report-path))]
      (println (pr-str result))
      (when-not (= :replayed (:status result)) (System/exit 1)))

    "request"
    (let [curriculum (edn/read-string
                      (slurp (or first-path curriculum-path)))
          checkpoint (day54/load-checkpoint
                      (or second-path default-checkpoint-path))
          result (write-next-request!
                  curriculum checkpoint (or third-path default-request-path)
                  (cond-> {}
                    fourth-argument
                    (assoc :target-count (Long/parseLong fourth-argument))))]
      (println (pr-str result)))

    "audit"
    (let [curriculum (edn/read-string
                      (slurp (or second-path curriculum-path)))
          checkpoint (day54/load-checkpoint
                      (or third-path default-checkpoint-path))]
      (println (pr-str (audit-next-batch
                        (or first-path default-statement-path)
                        curriculum checkpoint))))

    (let [catalog-path (or command default-catalog-path)
          checkpoint-path (or first-path default-checkpoint-path)
          curriculum (select-curriculum catalog-path)
          report (build-report catalog-path checkpoint-path curriculum)]
      (write-edn! (or third-path curriculum-path) curriculum)
      (write-edn! (or second-path report-path) report)
      (println (pr-str report))
      (when-not (= :passed (:status report)) (System/exit 1)))))
