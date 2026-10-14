(ns rainbow.main
  "Command-line front door of the open core.

      lein verify rainbow.math.finite.rational-argmax [more namespaces ...]
      lein verify --checkpoint artifacts/<dir>/checkpoint.edn.gz <namespace> ...
      lein verify --bundle [--reductions N] proof-bundle.edn ...
      lein reproduce rainbow.milestones.ahof-bisection [more ...]
      lein reproduce --all

  verify:
  For each namespace: replay the base checkpoint (every declaration in it is
  re-checked by the kernel on load), install the module through its own
  extend-environment, then re-check every theorem the module names against the
  kernel and print the axioms each one depends on. The exit code is non-zero if
  the checkpoint does not replay, a module fails to install, or any theorem is
  not :checked -- so the command is usable as a gate.

  reproduce: rebuild a milestone's checkpoint from source (its own `run`, from its
  recorded input checkpoint), write nothing, and compare the rebuilt checkpoint's
  content id with the recorded one's."
  (:require [clojure.edn :as edn]
            [clojure.string :as string]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]))

(def default-checkpoint
  "A late checkpoint of the open corpus; every module in the public tree installs on it."
  "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")

(defn- recheck [env id]
  (let [declaration (environment/declaration env id)]
    (:status (kernel/check env
                           (:rainbow/value declaration)
                           (:rainbow/type declaration)
                           (set (:rainbow/universes declaration))))))

(defn- quantifies-over-data?
  "True when a statement quantifies over data: one of its leading Pi binders ranges
  over a type outside Prop (numbers, vectors, a type variable), not merely over a
  hypothesis. A negation or implication between closed propositions is a Pi too,
  but it says something about specific values only, so it does not count."
  [env type universes]
  (loop [t type]
    (if (= :pi (first t))
      (let [binder (second t)
            closed? (not-any? #(and (vector? %) (= :bound (first %))) (tree-seq vector? seq binder))
            sort (when closed? (let [r (kernel/infer env binder universes)]
                                 (when (= :checked (:status r)) (:type r))))]
        (if (and sort (= :sort (first sort)) (not= [:sort [:zero]] sort))
          true
          (recur (nth t 2))))
      false)))

(defn- proof-is-reflexivity?
  "True when a proof term is, under its binders, an application of equality/reflexive:
  the statement holds by unfolding definitions, and says nothing beyond them."
  [env value]
  (let [refl (environment/resolve-id env 'equality/reflexive)
        body (loop [t value] (if (= :lam (first t)) (recur (nth t 2)) t))
        head (loop [t body] (if (= :app (first t)) (recur (second t)) t))]
    (and refl (= :const (first head)) (= refl (second head)))))

(defn verify-namespace
  "Installs ns-sym on base and re-checks its theorems. Returns
  {:namespace .. :theorems [{:name :id :status :axioms}] } or {:namespace .. :error ..}."
  [base ns-sym]
  (try
    (require ns-sym)
    (let [extend (ns-resolve ns-sym 'extend-environment)
          ids-fn (or (ns-resolve ns-sym 'theorem-ids) (ns-resolve ns-sym 'definition-ids))]
      (cond
        (nil? extend) {:namespace ns-sym :error "no extend-environment (not a proof module)"}
        :else
        (let [env (extend base)]
          (when-not (and (map? env)
                         (= environment/schema-version (:rainbow.environment/schema-version env))
                         (map? (:rainbow.environment/declarations env))
                         (map? (:rainbow.environment/aliases env))
                         (vector? (:rainbow.environment/order env)))
            (throw (ex-info "extend-environment did not return a declaration environment" {:namespace ns-sym})))
          (if (nil? ids-fn)
            ;; Installs others' theorems (a tactic or a bundle): installing is the check.
            {:namespace ns-sym :theorems [] :bundle? true}
            {:namespace ns-sym
             :theorems (vec (for [[name id] (ids-fn env)]
                              {:name name :id id
                               :status (if (and id (= id (environment/resolve-id env name)))
                                         (recheck env id)
                                         :alias-mismatch)
                               :axioms (kernel/axioms env id)
                               ;; :for-all when the statement quantifies over data, :instance when it is a
                               ;; statement about specific values (a worked instance)
                               ;; :for-all quantifies over data; :unfolding does too but holds by reflexivity
                               ;; (a definition unfolded); :instance is about specific values
                               :scope (let [d (environment/declaration env id)]
                                        (cond
                                          (not (quantifies-over-data? env (:rainbow/type d) (set (:rainbow/universes d)))) :instance
                                          (proof-is-reflexivity? env (:rainbow/value d)) :unfolding
                                          :else :for-all))}))}))))
    (catch Throwable t
      {:namespace ns-sym
       :error (str (.getMessage t) " "
                   (pr-str (-> t ex-data :result :error (select-keys [:alias :error/category]))))})))

(defn- ok? [result]
  (and (not (:error result))
       (or (:bundle? result) (seq (:theorems result)))
       (every? #(= :checked (:status %)) (:theorems result))))

(defn- print-result [{:keys [namespace error theorems] :as result}]
  (if error
    (println "FAIL " namespace "--" error)
    (do (println (if (ok? result) "OK   " "FAIL ") namespace
                 (if (:bundle? result)
                   "(installed; declares no theorems of its own)"
                   (let [c (frequencies (map :scope theorems))]
                     (str "(" (count theorems) " theorems: " (get c :for-all 0) " for all inputs, "
                          (get c :unfolding 0) " definitional unfoldings, "
                          (get c :instance 0) " worked instances)"))))
        (doseq [{:keys [name status axioms scope]} theorems]
          (println (format "       %-9s %-9s %s%s" (clojure.core/name status) (clojure.core/name scope) name
                           (if (seq axioms) (str "  axioms: " (pr-str (sort axioms))) "  axiom-free")))))))

(declare verify-namespace-main verify-bundles-main)

(defn- verify-main [args]
  (if (= "--bundle" (first args))
    (verify-bundles-main (rest args))
    (verify-namespace-main args)))

(defn- verify-namespace-main [args]
  (let [[cp nss] (if (= "--checkpoint" (first args))
                   [(second args) (drop 2 args)]
                   [default-checkpoint args])]
    (when (empty? nss)
      (println "usage: lein verify [--checkpoint path] <namespace> ...")
      (System/exit 2))
    (let [loaded (checkpoint/load-checkpoint cp)]
      (when-not (= :replayed (:status loaded))
        (println "FAIL checkpoint" cp "did not replay:" (pr-str (:status loaded)))
        (System/exit 1))
      (println "checkpoint" cp "replayed")
      (let [results (mapv #(verify-namespace (:environment loaded) (symbol %)) nss)]
        (run! print-result results)
        (every? ok? results)))))

;; ---------------------------------------------------------------- proof bundles

(defn- bundle-entries [env ids]
  (second
   (reduce (fn [[blocks entries] id]
             (let [declaration (environment/declaration env id)]
               (if-let [block-id (:rainbow/block-id declaration)]
                 (if (contains? blocks block-id)
                   [blocks entries]
                   [(conj blocks block-id)
                    (conj entries {:entry/kind :inductive-block
                                   :entry/value (assoc (:block/spec (environment/block env block-id))
                                                       :rainbow/id block-id)})])
                 [blocks (conj entries {:entry/kind :declaration :entry/value declaration})])))
           [#{} []] ids)))

(defn proof-bundle
  "A self-contained, re-checkable record of declarations proved on top of a public
  base: the base (a checkpoint plus the proof modules installed on it, in order),
  every new declaration or added declaration alias (in installation order),
  and the claims -- aliases with their ids and axiom closures. The declarations
  carry their proof terms, so the bundle can be checked by the kernel alone,
  without whatever program generated them. Ordinary declarations use schema 1.
  A bundle adding inductive blocks uses schema 2's ordered :entries, so each
  block is checked atomically before declarations that use its members."
  [{:keys [checkpoint modules base-env env claims meta reductions]}]
  (let [exported-ids (filter (fn [id]
                               (let [before (environment/declaration base-env id)
                                     after (environment/declaration env id)]
                                 (or (nil? before)
                                     (not= (:rainbow/aliases before) (:rainbow/aliases after)))))
                             (distinct (:rainbow.environment/order env)))
        entries (bundle-entries env exported-ids)
        blocks? (some #(= :inductive-block (:entry/kind %)) entries)]
    (assoc
     {:rainbow.bundle/schema-version (if blocks? 2 1)
     :base {:checkpoint checkpoint
            :modules (mapv str modules)
            :environment-id (environment/environment-id base-env)}
     :claims (into (sorted-map)
                   (for [alias claims
                         :let [id (environment/resolve-id env alias)]]
                     [alias {:id id :axioms (kernel/axioms env id)}]))
     ;; the kernel reduction budget the declarations were checked under. A budget is a resource limit, not
     ;; trust: a larger one only lets the check run longer, it cannot make a false proof pass.
     :check {:reductions (or reductions kernel/*reduction-budget*)}
      :meta meta}
     (if blocks? :entries :declarations)
     (if blocks? entries (mapv :entry/value entries)))))

(defn write-bundle! [path bundle]
  ;; Persist complete EDN regardless of the caller's diagnostic print settings.
  ;; Namespace-map lifting turns e.g. exported/true keys into Boolean true on read.
  (binding [*print-namespace-maps* false
            *print-length* nil *print-level* nil
            *print-meta* false *print-dup* false *print-readably* true]
    (spit path (str (pr-str bundle) "\n"))))

(declare check-bundle*)

(defn check-bundle
  "Replays a proof bundle through the kernel: the base checkpoint must replay, the
  named modules install on it to the recorded environment id, every declaration
  is re-checked by kernel/add-declaration (inductive blocks by add-inductive-block),
  and every claim resolves to its
  recorded id with its recorded axiom closure."
  ([bundle] (check-bundle bundle nil))
  ([bundle reductions]
   (try
     (binding [kernel/*reduction-budget* (max kernel/*reduction-budget*
                                              (or reductions 0)
                                              (or (get-in bundle [:check :reductions]) 0))]
       (check-bundle* bundle))
     (catch Throwable t
       {:ok? false :error (.getMessage t)}))))

(defn- kernel-reason
  "The most informative kernel category in a (nested) rejection: a budget
  exhaustion anywhere inside wins, because it means \"not decided\", not \"false\";
  otherwise the innermost category."
  [result]
  (let [categories (->> (tree-seq coll? seq result)
                        (filter map?)
                        (keep :error/category)
                        vec)]
    (or (some #{:kernel/resource-limit} categories)
        (peek categories))))

(def supported-bundle-schemas #{1 2})

(defn- bundle-payload-error [bundle]
  (case (:rainbow.bundle/schema-version bundle)
    1 (cond
        (contains? bundle :entries) "schema 1 uses :declarations, not :entries"
        (not (vector? (:declarations bundle))) "schema 1 requires a :declarations vector")
    2 (cond
        (contains? bundle :declarations) "schema 2 uses :entries, not :declarations"
        (not (vector? (:entries bundle))) "schema 2 requires an :entries vector")
    nil))

(defn- replay-bundle-entry [env {:entry/keys [kind value]}]
  (case kind
    :declaration (kernel/add-declaration env value)
    :inductive-block (kernel/add-inductive-block env value)
    {:status :rejected :error {:error/category :bundle/unknown-entry-kind :kind kind}}))

(defn- check-bundle* [bundle]
  (try
    (cond
      (not (contains? supported-bundle-schemas (:rainbow.bundle/schema-version bundle)))
      {:ok? false :error (str "not a proof bundle this version understands: :rainbow.bundle/schema-version is "
                              (pr-str (:rainbow.bundle/schema-version bundle))
                              ", expected one of " (pr-str supported-bundle-schemas))}
      (not (and (map? (:claims bundle)) (seq (:claims bundle))))
      {:ok? false :error "a proof bundle must name at least one claim in a :claims map"}
      (bundle-payload-error bundle)
      {:ok? false :error (bundle-payload-error bundle)}
      :else
    (let [{:keys [checkpoint modules environment-id]} (:base bundle)
          loaded (checkpoint/load-checkpoint checkpoint)]
      (if-not (= :replayed (:status loaded))
        {:ok? false :error (str "base checkpoint did not replay: " checkpoint)}
        (let [base (reduce (fn [env m]
                             (let [s (symbol m)]
                               (require s)
                               ((ns-resolve s 'extend-environment) env)))
                           (:environment loaded) modules)]
          (if-not (= environment-id (environment/environment-id base))
            {:ok? false :error "the base modules did not reproduce the recorded environment id"}
            (let [entries (if (= 2 (:rainbow.bundle/schema-version bundle))
                            (:entries bundle)
                            (mapv #(hash-map :entry/kind :declaration :entry/value %) (:declarations bundle)))
                  result (reduce (fn [env entry]
                                   (let [r (replay-bundle-entry env entry)]
                                     (if (= :accepted (:status r))
                                       (:environment r)
                                       (reduced {:rejected (or (get-in entry [:entry/value :rainbow/id]) :unnamed)
                                                 :cause r}))))
                                 base entries)]
              (if (:rejected result)
                {:ok? false :error (str "kernel rejected bundle entry " (:rejected result)
                                        (when-let [why (kernel-reason (:cause result))] (str " (" why ")"))
                                        (when (= :kernel/resource-limit (kernel-reason (:cause result)))
                                          (str "; the reduction budget was " kernel/*reduction-budget*
                                               ", try --reductions with a larger value")))}
                {:ok? (every? (fn [[alias {:keys [id axioms]}]]
                                (and (= id (environment/resolve-id result alias))
                                     (= :checked (recheck result id))
                                     (= axioms (kernel/axioms result id))))
                              (:claims bundle))
                 :claims (into (sorted-map)
                               (for [[alias {:keys [id]}] (:claims bundle)]
                                 (let [resolved (environment/resolve-id result alias)
                                       status (some->> resolved (recheck result))
                                       actual (some->> resolved (kernel/axioms result))
                                       recorded (get-in bundle [:claims alias :axioms])]
                                   [alias {:id id :resolved resolved :status status :axioms actual
                                           :problems (cond-> []
                                                       (not= id resolved) (conj (str "resolves to " resolved ", recorded " id))
                                                       (not= :checked status) (conj "does not re-check")
                                                       (not= recorded actual) (conj (str "recorded axioms " (pr-str recorded)
                                                                                         " but the kernel computes " (pr-str actual))))}])))}))))))
    )
    (catch Throwable t
      {:ok? false :error (.getMessage t)})))

(defn- verify-bundles-main [args]
  ;; mapv, not for: every bundle is checked and reported even after one fails
  (try
    (let [[reductions paths] (if (= "--reductions" (first args))
                               [(Long/parseLong (second args)) (drop 2 args)]
                               [nil args])]
      (when (empty? paths)
        (throw (ex-info "usage: lein verify --bundle [--reductions N] <bundle> ..." {})))
      (every? true?
              (mapv (fn [path]
                      (let [{:keys [ok? error claims]}
                            (try (check-bundle (edn/read-string (slurp path)) reductions)
                                 (catch Throwable t {:ok? false :error (.getMessage t)}))]
                        (println (if ok? "OK   " "FAIL ") path (if error (str "-- " error) ""))
                        (doseq [[alias {:keys [status axioms problems]}] claims]
                          (println (format "       %-9s %s%s%s" (some-> status name) alias
                                           (if (seq axioms) (str "  axioms: " (pr-str (sort axioms))) "  axiom-free")
                                           (if (seq problems) (str "  -- " (string/join "; " problems)) ""))))
                        (flush)
                        (boolean ok?)))
                    paths)))
    (catch Throwable t
      (println "FAIL --" (.getMessage t))
      false)))

;; ---------------------------------------------------------------- reproduce

(defn reproduce-milestone
  "Rebuilds a milestone's checkpoint from source and compares it with the recorded one.

  A reproducible milestone namespace defines `run` (input checkpoint path -> {:checkpoint :report}),
  `default-input-checkpoint-path` and `checkpoint-path`. `run` writes nothing: the recorded evidence is
  only read. The comparison is by content id -- the hash of the whole checkpoint value (environment,
  mappings, remaining targets) -- so equal ids mean the rebuild produced the same declarations."
  [ns-sym]
  (try
    (require ns-sym)
    (let [run (ns-resolve ns-sym 'run)
          input (some-> (ns-resolve ns-sym 'default-input-checkpoint-path) deref)
          recorded-path (some-> (ns-resolve ns-sym 'checkpoint-path) deref)]
      (if-not (and run input recorded-path)
        {:namespace ns-sym :error "not a reproducible milestone (needs run, default-input-checkpoint-path, checkpoint-path)"}
        (let [recorded (checkpoint/load-checkpoint recorded-path)
              rebuilt (:checkpoint (run input))
              rebuilt-id (:rainbow.checkpoint/id rebuilt)]
          {:namespace ns-sym
           :recorded-path recorded-path
           :recorded-status (:status recorded)
           :recorded-id (:checkpoint/id recorded)
           :rebuilt-id rebuilt-id
           :match? (and (= :replayed (:status recorded))
                        (some? rebuilt-id)
                        (= rebuilt-id (:checkpoint/id recorded)))})))
    (catch Throwable t
      {:namespace ns-sym :error (str (.getMessage t))})))

(defn reproducible-milestones
  "Every namespace under src/rainbow/milestones that has the reproducible shape (found by reading the
  source tree, so a new milestone is picked up without a list to maintain)."
  []
  (->> (file-seq (java.io.File. "src/rainbow/milestones"))
       (filter #(.endsWith (.getName ^java.io.File %) ".clj"))
       (keep (fn [f]
               (let [text (slurp f)]
                 (when (and (re-find #"\(defn run \[" text)
                            (re-find #"\(def default-input-checkpoint-path" text)
                            (re-find #"\(def checkpoint-path" text))
                   (second (re-find #"\(ns ([\w.\-]+)" text))))))
       sort
       (mapv symbol)))

(defn- reproduce-main [args]
  (let [nss (if (= ["--all"] (vec args)) (reproducible-milestones) (map symbol args))]
    (when (empty? nss)
      (println "usage: lein reproduce <milestone-namespace> ... | lein reproduce --all")
      (System/exit 2))
    (let [results (mapv (fn [n] (let [r (reproduce-milestone n)]
                                  (if (:error r)
                                    (println "FAIL " n "--" (:error r))
                                    (println (if (:match? r) "SAME " "DIFF ") n
                                             (str "recorded " (:recorded-id r) " (" (name (:recorded-status r)) ")"
                                                  (when-not (:match? r) (str ", rebuilt " (:rebuilt-id r))))))
                                  (flush)
                                  r))
                        nss)]
      (println (count (filter :match? results)) "of" (count results) "rebuilt checkpoints match their recorded content id")
      (every? :match? results))))

(defn -main
  "lein verify ... | lein reproduce ... (the first argument names the command)."
  [& [command & args]]
  (let [ok (case command
             "verify" (verify-main args)
             "reproduce" (reproduce-main args)
             (do (println "usage: lein verify ... | lein reproduce ...") (System/exit 2)))]
    (shutdown-agents)
    (System/exit (if ok 0 1))))
