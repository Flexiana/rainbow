(ns rainbow.evidence
  "Build an evidence bundle from what the repository can actually demonstrate.

  Evidence has to be something a grantmaker or a buyer's auditor
  can check, and forbids fabricating novelty, adoption, TRL or benchmark
  superiority. So this namespace has one rule: EVERY FIELD IS READ FROM THE
  REPOSITORY OR OMITTED. Nothing is estimated, inferred from intent, or carried
  over from a previous run.

  Where a figure would require running the suite or the kernel, the bundle
  records the COMMAND that produces it rather than a remembered number, so a
  reader reproduces it instead of trusting it.

  Deliberately absent, because the repository cannot currently substantiate them:
  adoption, users, partners, citations, TRL, benchmark superiority against
  external solvers, and any cross-validation against Lean, Rocq or Isabelle."
  (:require [rainbow.source :as source]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as string]
            [rainbow.history.release-gate :as v1]))

(defn- clj-files [dir]
  (->> (file-seq (io/file dir))
       (filter #(string/ends-with? (.getName ^java.io.File %) ".clj"))))

(defn- line-count [f] (with-open [r (io/reader f)] (count (line-seq r))))

(def trusted-paths
  ["src/rainbow/canonical.clj" "src/rainbow/term.clj"
   "src/rainbow/environment.clj" "src/rainbow/kernel.clj"])

(defn declared-aliases
  "Every alias declared anywhere in src, read out of `:name 'alias` fields.

  NOTE the known blind spot: modules that GENERATE declarations pass the name in
  as an argument, so this undercounts them. It is reported as a floor, not a
  total, and the manifest count is reported separately rather than summed."
  []
  (into #{}
        (mapcat (fn [f]
                  (map second
                       (re-seq #":name '([A-Za-z][A-Za-z0-9./*+!?<>=_-]*)" (slurp f)))))
        (source/clj-files "rainbow")))

(defn manifest-files
  "Every file the manifest directory offers, whether or not it parses."
  []
  (->> (file-seq (io/file "artifacts/manifests"))
       (filter #(string/ends-with? (.getName ^java.io.File %) ".edn"))
       vec))

(defn read-manifest
  "One manifest, or a MARKER saying it could not be read.

  A manifest that does not parse used to reach the audit as a bare reader error
  naming no file -- `Invalid token: T:` and nothing else -- so `lein cli claims`
  died before printing its result line and an operator grepping for a verdict saw
  neither the verdict nor the file. The marker carries the path so the audit can
  report it as a FAILING row instead of dying: an unreadable manifest is a finding,
  not an absence."
  [f]
  (let [path (str f)]
    (try (assoc (edn/read-string (slurp f)) :manifest/path path)
         (catch Throwable t
           {:manifest/path path
            :manifest/unreadable (or (.getMessage t) (str (class t)))}))))

(defn manifests
  "Per-algorithm manifests, which are the only place maturity levels are claimed.

  Strict: an unreadable manifest throws, but the error NAMES THE FILE. Callers that
  want to report rather than die (the claims audit) read `manifest-files` and
  `read-manifest` themselves and look for `:manifest/unreadable`."
  []
  (let [read (mapv read-manifest (manifest-files))
        bad (filterv :manifest/unreadable read)]
    (when (seq bad)
      (throw (ex-info (str "unreadable manifest(s): "
                           (string/join ", " (map (fn [m] (str (:manifest/path m)
                                                              " -- "
                                                              (:manifest/unreadable m)))
                                                  bad)))
                      {:unreadable (mapv :manifest/path bad)})))
    read))

(defn- maturity-histogram [ms]
  (->> ms (map :maturity-level) (remove nil?) frequencies (into (sorted-map))))

(defn- open-gaps [ms]
  (vec (for [m ms g (:known-gaps m)
             :when (= :open (:status g))]
         {:algorithm (:id m) :gap (:gap g) :blocking (boolean (:blocking g))})))

(defn build
  "The bundle. Every number here is counted from the working tree at call time."
  []
  (let [aliases (declared-aliases)
        ms (manifests)
        src (source/clj-files "rainbow")
        tests (->> (file-seq (io/file "test"))
                   (filter #(string/ends-with? (.getName ^java.io.File %) "_test.clj")))]
    {:evidence/generated-from :working-tree
     :corpus
     {:declared-aliases-floor (count aliases)
      :source-files (count src)
      :source-lines (reduce + (map line-count src))
      :test-namespaces (count tests)}
     :compactness
     ;; The classification rule is READ FROM Gate F rather than restated here,
     ;; so the two cannot drift into disagreeing about what a reader must audit.
     (let [corpus? (fn [^java.io.File f]
                     (boolean (some #(string/starts-with? (source/repo-path f) %)
                                    v1/corpus-prefixes)))
           machinery (remove corpus? src)
           corpus (filter corpus? src)]
       {:audited-machinery-lines (reduce + (map line-count machinery))
        :audited-machinery-cap :none
        :proof-corpus-lines (reduce + (map line-count corpus))
        :proof-corpus-cap :none
        :corpus-prefixes v1/corpus-prefixes
        :note "Gate F caps the first number and leaves the second free."})
     :trusted-base
     {:paths trusted-paths
      :lines (reduce + (map (comp line-count source/file) trusted-paths))
      :note "Gate A pins this exactly; see corpus/v1.clj."}
     :maturity
     {:manifests (count ms)
      :levels (maturity-histogram ms)
      :algorithms (mapv (fn [m] {:id (:id m)
                                 :level (:maturity-level m)
                                 :target (:target-level m)
                                 :verified (:what-is-actually-verified m)}) ms)}
     :open-gaps (open-gaps ms)
     :reproduce
     {:full-suite ["scripts/run-suite-chunked.sh" "40" "target/evidence-suite.tsv"]
      :per-algorithm (vec (keep :verification-command ms))
      :note "Suite counts are deliberately NOT cached here. Run the command."}
     :not-claimed
     ["adoption, users, partners" "citations" "TRL"
      "benchmark superiority against external solvers"
      "cross-validation against Lean, Rocq or Isabelle"
      "any Level-6 implementation"]}))

(defn -main [& args]
  (let [bundle (build)]
    (if (some #{"--edn"} args)
      (prn bundle)
      (do
        (println "Rainbow evidence bundle")
        (println "  aliases (floor):  " (get-in bundle [:corpus :declared-aliases-floor]))
        (println "  source files:     " (get-in bundle [:corpus :source-files]))
        (println "  source lines:     " (get-in bundle [:corpus :source-lines]))
        (println "  test namespaces:  " (get-in bundle [:corpus :test-namespaces]))
        (println "  trusted base:     " (get-in bundle [:trusted-base :lines]) "lines")
        (println "  audited machinery:" (get-in bundle [:compactness :audited-machinery-lines]) "lines")
        (println "  checked corpus:   " (get-in bundle [:compactness :proof-corpus-lines])
                 "lines, uncapped by design")
        (println "  manifests:        " (get-in bundle [:maturity :manifests])
                 "levels" (get-in bundle [:maturity :levels]))
        (println "  open gaps:        " (count (:open-gaps bundle))
                 "of which blocking:" (count (filter :blocking (:open-gaps bundle))))
        (println "  NOT claimed:      " (string/join "; " (:not-claimed bundle)))))))
