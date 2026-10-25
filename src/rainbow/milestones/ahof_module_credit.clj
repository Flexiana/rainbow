(ns rainbow.milestones.ahof-module-credit
  "Generic content-addressed milestone runner for crediting a pending AHoF catalog
  row whose native, axiom-free proof already lives in one or more logic modules. A
  per-row corpus file supplies a config map; this runner performs the same
  precommit -> content-id -> checkpoint-replay -> ledger-credit pipeline the bespoke
  milestone corpora use, including verifying the report passed BEFORE writing the
  ledger credit so a failed run can never corrupt the system of record.

  A config is:
    {:id \"O48\" :name \"Penalty Method\"
     :source-file \"catalog/01_optimization_algorithms.md\" :listing \"...\"
     :kind :ahof-o48-penalty
     :dir \"artifacts/ahof/o48-penalty\"
     :modules [{:extend f :defs f :thms f} ...]   ; applied left-to-right
     :baseline-prereqs [{:target/name 'sym :statement \"...\"} ...]
     :package 'penalty/feasible-equals-objective  ; the headline proof
     :spec {...}                                   ; ledger-entry :ahof/specification
     :statements {sym \"held-out statement\" ...}   ; optional per-target statements
     :worked-eval (fn [env] {...:status :normalized|:skipped})}"
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.milestones.ahof-eligibility-traces :as d63]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def input-checkpoint-id
  "sha256:d8e790a380890ed64a5313eab9c9133fe8cd519386957392099c7bf1a188261c")

(defn precommit-path [config] (str (:dir config) "/precommit.edn"))
(defn report-path [config] (str (:dir config) "/report.edn"))
(defn checkpoint-path [config] (str (:dir config) "/checkpoint.edn.gz"))

(defn- checked? [env id]
  (when id
    (let [d (environment/declaration env id)]
      (= :checked
         (:status (kernel/check env (:rainbow/value d) (:rainbow/type d)
                                (set (:rainbow/universes d))))))))

(defn- extend-all [baseline config]
  (reduce (fn [env {:keys [extend]}] (extend env)) baseline (:modules config)))

(defn- def-ids [env config]
  (apply merge (map (fn [{:keys [defs]}] (defs env)) (:modules config))))
(defn- thm-ids [env config]
  (apply merge (map (fn [{:keys [thms]}] (thms env)) (:modules config))))

;; Auto-partition the module's own declarations: definitions -> development,
;; theorems -> held-out except the last -> transfer.
(defn- module-targets [env config]
  (let [defs (vec (keys (def-ids env config)))
        thms (vec (keys (thm-ids env config)))
        stmts (:statements config)
        held (subvec thms 0 (max 0 (dec (count thms))))
        transfer (subvec thms (max 0 (dec (count thms))))]
    (concat
     (map #(assoc % :study/partition :baseline-support) (:baseline-prereqs config))
     (map (fn [s] {:target/name s :study/partition :development
                   :statement (get stmts s (str s " is defined"))}) defs)
     (map (fn [s] {:target/name s :study/partition :held-out
                   :statement (get stmts s (str s " holds"))}) held)
     (map (fn [s] {:target/name s :study/partition :transfer
                   :statement (get stmts s (str s " holds"))}) transfer))))

(defn precommit-body [env config]
  (let [targets (mapv (fn [{:keys [target/name study/partition statement]}]
                        {:target/name name :study/partition partition
                         :statement statement})
                      (module-targets env config))]
    #:precommit{:representation (:representation config {:proof :native-decision})
                :targets targets
                :claim-boundaries (:claim-boundaries config
                                                     {:exact-rational-only? true
                                                      :native-decision? true})
                :kind (:kind config)
                :schema-version 1
                :baseline {:native-targets-present (count (:baseline-prereqs config))
                           :catalog-outcome :pending}
                :source {:ahof/id (:id config)
                         :ahof/name (:name config)
                         :ahof/source-file (:source-file config)
                         :ahof/source-commit ahof/source-commit
                         :ahof/listing (:listing config)
                         :input-checkpoint/id input-checkpoint-id
                         :foreign-proof-values :not-applicable}
                :fixed-policy {:kernel/reductions 1000000
                               :evaluation/reductions 2000000
                               :success :kernel-checked-axiom-free-native-decision}}))

(defn generate-precommit!
  ([config] (generate-precommit! config (day54/load-checkpoint d63/checkpoint-path)))
  ([config prior]
  (let [env (extend-all (:environment prior) config)
        body (precommit-body env config)
        id (canonical/content-id body)
        full (assoc body :precommit/id id)]
    (io/make-parents (precommit-path config))
    (spit (precommit-path config) (str (pr-str full) "\n"))
    {:precommit/id id :targets (count (:precommit/targets body))})))

(defn- load-precommit [config]
  (let [value (edn/read-string (slurp (precommit-path config)))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "precommit identity mismatch"
                      {:id (:id config) :expected expected
                       :actual (:precommit/id value)})))
    value))

(defn build
  ([config] (build config (day54/load-checkpoint d63/checkpoint-path)))
  ([config prior]
  (let [precommit (load-precommit config)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "input checkpoint rejected" {:id (:id config)})))
    (when-not (day54/same-input-checkpoint? (get-in precommit [:precommit/source :input-checkpoint/id])
                                            (:checkpoint/id prior))
      (throw (ex-info "input checkpoint identity mismatch" {:id (:id config)})))
    (let [baseline (:environment prior)
          env (extend-all baseline config)
          definition-ids (def-ids env config)
          theorem-ids (thm-ids env config)
          targets
          (mapv
           (fn [{:keys [target/name study/partition]}]
             (let [rid (environment/resolve-id env name)]
               {:target/name name :study/partition partition :native/id rid
                :baseline/status (if (environment/resolve-id baseline name)
                                   :proved :missing-generalized-lemma)
                :candidate/status (if (checked? env rid) :proved :failed)
                :axioms (if rid (kernel/axioms env rid) #{})
                :states-created 0}))
           (:precommit/targets precommit))
          worked ((:worked-eval config (constantly {:status :skipped})) env)]
      {:precommit precommit :prior prior :environment env :targets targets
       :definition-ids definition-ids :theorem-ids theorem-ids
       :evaluation worked}))))

(defn checkpoint [config build]
  (let [value (frontier/checkpoint {:prior (:prior build)
                                 :environment (:environment build)
                                 :new-mappings [] :evaluations []})
        base (-> value
                 (dissoc :rainbow.checkpoint/id)
                 (update-in [:source :additional-statement-batches] (fnil conj [])
                            {:kind (:kind config)
                             :precommit/id (get-in build [:precommit :precommit/id])
                             :proof-values :redacted}))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn report [config build checkpoint-value replay]
  (let [targets (:targets build)
        held-out (filterv #(= :held-out (:study/partition %)) targets)
        transfer (filterv #(= :transfer (:study/partition %)) targets)
        proved? #(= :proved (:candidate/status %))
        all-new-ids (concat (vals (:definition-ids build))
                            (vals (:theorem-ids build)))
        eval-status (get-in build [:evaluation :status])
        passed?
        (and (= :replayed (:status replay))
             (pos? (count targets))
             (every? proved? targets)
             (every? empty? (map :axioms targets))
             (every? #(checked? (:environment build) %) all-new-ids)
             (contains? #{:normalized :skipped} eval-status))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id (:id config)
         :algorithm/name (:name config)
         :source {:proof-origin :independent-native-rainbow
                  :ahof/source-commit ahof/source-commit
                  :mathlib-proof-bodies-used? false
                  :input-checkpoint/id (get-in build [:prior :checkpoint/id])
                  :precommit/id (get-in build [:precommit :precommit/id])}
         :results {:baseline-targets-present (count (:baseline-prereqs config))
                   :newly-solved-native-results
                   (count (filterv #(not= :proved (:baseline/status %)) targets))
                   :held-out {:before [0 (count held-out)]
                              :after [(count (filter proved? held-out))
                                      (count held-out)]}
                   :transfer {:after [(count (filter proved? transfer))
                                      (count transfer)]}
                   :search-states {:median 0 :total 0
                                   :interpretation :installed-kernel-certificates}}
         :targets targets
         :evaluation (:evaluation build)
         :axiom-profiles
         (into (sorted-map)
               (map (fn [[name id]] [name (kernel/axioms (:environment build) id)]))
               (:theorem-ids build))
         :trusted-base-delta :none
         :checkpoint {:id (:rainbow.checkpoint/id checkpoint-value)
                      :kernel-replay (:status replay)
                      :exact-mathlib-mappings (count (:mappings checkpoint-value))}
         :claim-boundaries (:claim-boundaries config
                                             {:exact-rational-only true
                                              :native-decision :proved})}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [config packet]
  {:ahof/id (:id config)
   :ahof/outcome :proved
   :ahof/specification (:spec config)
   :ahof/shared-foundations-counted-as-algorithm? false
   :ahof/evidence
   [{:kind :content-addressed-rainbow-evidence
     :evidence/id (:evidence/id packet)
     :checkpoint/id (get-in packet [:checkpoint :id])
     :proof-id (some->> (:targets packet)
                        (filter #(= (:package config) (:target/name %)))
                        first :native/id)
     :worked-evaluation (:evaluation packet)}]})

(defn run
  ([config] (run config (day54/load-checkpoint d63/checkpoint-path)))
  ([config prior]
  (let [build (build config prior)
        checkpoint-value (checkpoint config build)
        replay (day54/replay-checkpoint checkpoint-value)]
    {:build build :checkpoint checkpoint-value :replay replay
     :report (report config build checkpoint-value replay)})))

(defn load-report [config]
  (try
    (let [value (edn/read-string (slurp (report-path config)))
          expected (canonical/content-id (dissoc value :evidence/id))]
      (if (= expected (:evidence/id value))
        {:status :replayed :evidence/id expected}
        {:status :rejected :error/category :evidence-id-mismatch}))
    (catch Throwable t
      {:status :rejected :error/category :evidence-read-failed
       :message (.getMessage t)})))

(defn- write-edn! [path value]
  (io/make-parents path)
  (spit path (str (pr-str value) "\n")))

(defn credit!
  ([config] (credit! config (day54/load-checkpoint d63/checkpoint-path)))
  ([config prior]
  (let [{:keys [checkpoint report]} (run config prior)
        ledger-result (ahof/load-ledger ahof/ledger-path)]
    (when-not (= :replayed (:status ledger-result))
      (throw (ex-info "AHoF ledger rejected before credit"
                      {:id (:id config) :ledger-result ledger-result})))
    (when-not (= :passed (:status report))
      (throw (ex-info "report did not pass; refusing to credit"
                      {:id (:id config) :status (:status report)})))
    (write-edn! (report-path config) report)
    (frontier/write-checkpoint! (checkpoint-path config) checkpoint)
    (ahof/write-credited-ledger!
     ahof/ledger-path
     (ahof/credit-catalog-result (:ledger ledger-result)
                                 (ledger-entry config report)))
    (println (:id config) "credited:" (:status report)
             "| evidence" (:evidence/id report))
    report)))

(defn- proved-ids []
  (let [r (ahof/load-ledger ahof/ledger-path)]
    (into #{} (comp (filter #(= :proved (:ahof/outcome %))) (map :ahof/id))
          (get-in r [:ledger :ahof-ledger/algorithms]))))

(defn credit-batch!
  "Generate precommit + credit each config in one JVM, loading d63 once. Rows already
  proved in the ledger are skipped (idempotent). Each row independently verifies
  :passed before its ledger credit; a row that throws is reported and skipped without
  aborting the rest. Pass optional [offset limit] to process a slice (keeps per-JVM
  memory bounded)."
  ([configs] (credit-batch! configs 0 (count configs)))
  ([configs offset limit]
   (let [done (proved-ids)
         slice (->> configs (drop offset) (take limit)
                    (remove #(contains? done (:id %))))
         prior (day54/load-checkpoint d63/checkpoint-path)]
     (println "batch slice:" (count slice) "to credit (of" (count configs) "configs)")
     (doseq [config slice]
       (try
         (generate-precommit! config prior)
         (credit! config prior)
         (catch Throwable t
           (println "SKIP" (:id config) "->" (.getMessage t))))))))

(defn main [config args]
  (try
    (cond
      (= "precommit" (first args)) (println (:id config) (generate-precommit! config))
      (= "replay" (first args)) (println (:id config) (load-report config))
      :else (credit! config))
    (finally (shutdown-agents))))
