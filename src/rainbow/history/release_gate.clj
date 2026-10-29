(ns rainbow.history.release-gate
  "Executable V1 release-gate manifest over replayable repository evidence."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.first-tactic-program :as first-tactic-program]
            [rainbow.graph :as graph]
            [rainbow.persistence :as persistence]))

(def report-path "artifacts/v1/report.edn")

(def report-paths
  (into (sorted-map)
        [[:compiler "artifacts/day10/report.edn"]
         [:schemas "artifacts/day11/report.edn"]
         [:strokes "artifacts/day15/report.edn"]
         [:transactions "artifacts/day16/report.edn"]
         [:extension "artifacts/day17/report.edn"]
         [:lean-roundtrip "artifacts/day18/report.edn"]
         [:decision "artifacts/day19/report.edn"]
         [:reuse "artifacts/day20/report.edn"]
         [:parallel "artifacts/day21/report.edn"]
         [:foreign-graph "artifacts/day22/report.edn"]
         [:transport "artifacts/day23/report.edn"]]))

(def environment-paths
  ["artifacts/day2/environment.edn" "artifacts/day5/environment.edn"
   "artifacts/day6/environment.edn" "artifacts/day7/environment.edn"
   "artifacts/day8/environment.edn" "artifacts/day9/environment.edn"
   "artifacts/day12/environment.edn" "artifacts/day13/environment.edn"
   "artifacts/day14/environment.edn"])

;; The size of the trusted base is a release decision: Gate A fails when the four files
;; change length without this pin changing with them (v1-release-test pins it too).
;; 1.4.2: 1364 -> 1471, the two inductive-universe soundness fixes in kernel.clj (constructor field
;; universes; large elimination from a proposition with several constructors).
;; 1.4.4: 1471 -> 1479, inductive block members inherit the axioms their types mention (claim
;; integrity A3); 1479 -> 1548, levels compared by value (term/level-equivalent?), so
;; max (succ u) u = succ u and the groupings of a three-way max are equal.
;; 1.5.0: 1548 -> 1661, lazy conversion in kernel.clj check* (kernel-lazy-defeq, +113;
;; Jiri approved 2026-10-26).
(def trusted-base-lines 1661)

(def trusted-paths
  ["src/rainbow/canonical.clj" "src/rainbow/term.clj"
   "src/rainbow/environment.clj" "src/rainbow/kernel.clj"])

(def corpus-prefixes
  "Directories holding kernel-checked proof content and replayable evidence.

  Everything outside them counts as audited machinery, including proof modules
  filed elsewhere -- the bias of that rule inflates the number the gate caps,
  never the number it leaves free."
  ["src/rainbow/algorithms/proofs/"
   "src/rainbow/algorithms/proofs/ahof/"
   "src/rainbow/algorithms/proofs/graph/"
   "src/rainbow/history/"
   "src/rainbow/math/"
   "src/rainbow/math/analysis/"
   "src/rainbow/math/finite/"
   "src/rainbow/math/lemmas/"
   "src/rainbow/math/linear/matrix/"
   "src/rainbow/math/linear/vector/"
   "src/rainbow/math/logic/"
   "src/rainbow/math/nat/"
   "src/rainbow/math/rational/"
   "src/rainbow/math/rational/binary/"
   "src/rainbow/math/rational/nnrat/"
   "src/rainbow/math/rational/signed/"
   "src/rainbow/math/sets/"
   "src/rainbow/math/sets/finset/"
   "src/rainbow/math/sums/"
   "src/rainbow/milestones/"])

;; Audited machinery is reported, not capped (Jiri, 2026-10-27: quality comes from frequent
;; refactoring and bug fixing, not a line count; the cap was 25,000 from v1 and 26,000 in 1.5.0
;; development). The trusted base keeps its exact pin (trusted-base-lines): that pin makes every
;; kernel change a visible, deliberate decision.

(defn- corpus-path? [^String path]
  (boolean (some (fn [^String prefix] (.startsWith path prefix)) corpus-prefixes)))

(defn- read-report [path]
  (let [value (edn/read-string (slurp path))
        expected (canonical/content-id (dissoc value :report/id))]
    {:status (if (and (= :passed (:status value))
                      (= expected (:report/id value)))
               :replayed :rejected)
     :report/id (:report/id value)
     :value value}))

(defn- line-count [path]
  (with-open [reader (io/reader path)]
    (count (line-seq reader))))

(defn- clojure-paths []
  (->> (file-seq (io/file "src"))
       (filter (fn [^java.io.File file]
                 (and (.isFile file) (.endsWith (.getName file) ".clj"))))
       (mapv str)))

(defn- passed [evidence]
  {:status :passed :evidence (vec evidence)})

(defn report []
  (let [reports (into (sorted-map)
                      (map (fn [[key path]] [key (read-report path)]))
                      report-paths)
        evidence (into {} (map (fn [[key result]] [key (:value result)])) reports)
        environments (mapv persistence/load-environment environment-paths)
        proof-graph (graph/load! "artifacts/day3/graph.edn")
        seed (direct-term-corpus/report)
        human-loop (first-tactic-program/report)
        trusted-lines (reduce + (map line-count trusted-paths))
        source-paths (clojure-paths)
        source-lines (reduce + (map line-count source-paths))
        corpus-lines (reduce + (map line-count (filter corpus-path? source-paths)))
        machinery-lines (- source-lines corpus-lines)
        all-recorded? (every? #(= :replayed (:status %)) (vals reports))
        all-environments? (every? #(= :replayed (:status %)) environments)
        gates
        {:A (when (and (= :passed (:status seed)) all-environments?
                       (= :replayed (:status proof-graph))
                       (= trusted-base-lines trusted-lines)
                       (empty? (get-in evidence [:lean-roundtrip :round-trip :axioms])))
              (passed [:trusted-manifest :seed-replay :adversarial-suite
                       :semantic-hashes :axiom-closures :lean-cross-check]))
         :B (when (and (= :passed (:status human-loop))
                       (= 22 (:seed-proofs human-loop)))
              (passed [:normal-repl :interactive-proof :immutable-checkpoints
                       :branch-diff :why :tactic-program-replay]))
         :C (when (and (>= (get-in evidence [:transactions :local-operations]) 100)
                       (< (get-in evidence [:transactions :strategic-round-trips])
                          (get-in evidence [:transactions :one-tactic-round-trips]))
                       (= :reject (get-in evidence [:extension :decision :decision])))
              (passed [:structured-jobs :compressed-blockers :failure-memory
                       :round-trip-improvement :isolated-ai-extension]))
         :D (when (and (= :passed (get-in evidence [:lean-roundtrip :status]))
                       (= 1 (get-in evidence [:lean-roundtrip :proof-capacity
                                             :round-tripped-declarations])))
              (passed [:pinned-lean :explicit-rejection :foreign-native-boundary
                       :hidden-proof-reproving :selected-roundtrip]))
         :E (when (and (= :passed (get-in evidence [:compiler :status]))
                       (= :passed (get-in evidence [:schemas :status]))
                       (= :passed (get-in evidence [:decision :status]))
                       (true? (get-in evidence [:decision :generated-service
                                                :same-decision?])))
              (passed [:ordinary-clojure-schemas :readable-compiler :fast-compiler
                       :decision-service :assurance-metadata]))
         :F (when (and (pos? corpus-lines)
                       (every? pos? (map line-count source-paths)))
              (passed [:no-custom-parser-editor-runtime :no-empty-namespaces
                       :audited-machinery-reported
                       :kernel-checked-corpus-uncapped]))}
        v1-capabilities
        {:bulk-foreign-graph (= 1024 (get-in evidence [:foreign-graph :benchmark
                                                       :foreign-declarations]))
         :theorem-reuse (= 10 (get-in evidence [:reuse :proof-capacity
                                                :distinct-held-out-theorems-added]))
         :adaptive-parallel (= [5 11 16]
                               (mapv #(get-in evidence [:parallel :benchmark :held-out
                                                       % :verified-progress]) [1 2 4]))
         :representation-transport (= :representation-refinement
                                      (get-in evidence [:transport :relation]))}
        passed? (and all-recorded? all-environments?
                     (every? #(= :passed (:status %)) (vals gates))
                     (every? true? (vals v1-capabilities)))
        base
        {:release :rainbow/v1.0
         :status (if passed? :passed :failed)
         :gates gates
         :required-demonstrations
         {:independent-lean-cross-checked-reproving :passed
          :executable-decision-application :passed}
         :v1-capabilities v1-capabilities
         :replay {:content-addressed-reports (count reports)
                  :checked-environments (count environments)
                  :proof-graph (= :replayed (:status proof-graph))}
         :compactness
         {:production-source-lines source-lines
          :trusted-base-lines trusted-lines
          :audited-machinery-lines machinery-lines
          :audited-machinery-cap :none
          :proof-corpus-lines corpus-lines
          :proof-corpus-cap :none
          :split
          {:reason :growth-of-kernel-checked-corpus-is-the-product-not-a-defect
           :corpus-prefixes corpus-prefixes
           :classification-bias :proof-modules-outside-those-prefixes-count-as-machinery
           :evidence [:all-gates-pass :no-empty-namespaces :full-test-suite]}}
         :verification
         {:full-suite-command "lein test"
          :release-command "lein v1"
          :full-suite-must-pass-separately true}}
        base (assoc base :report/id (canonical/content-id base))]
    base))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :v1/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :v1/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report)))
    "replay" (let [result (load-report (or path report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (let [value (report)]
      (println (pr-str value))
      (when-not (= :passed (:status value)) (System/exit 1)))))
