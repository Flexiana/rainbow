(ns rainbow.ahof-ledger-integrity-test
  "Fast guard on the invariant a filename collision broke in August 2026.

  The AHoF ledger is the system of record for the catalog claim, and each proved
  row names the declarations that back it. Nothing checked that those
  declarations still EXIST. When `logic/ahof_policy_evaluation.clj` was
  overwritten by an unrelated proof, the D20 row went on claiming symbols no
  module declared any more, and the only test that noticed lived in a full suite
  long enough that it is rarely run -- so the ledger was wrong for four days.

  This test is deliberately cheap: it reads the ledger and scans declaration
  names out of the source, with no environment, no checkpoint and no kernel. It
  runs in well under a second, which is the point. A guard that is only exercised
  by a forty-five minute gate is not protecting anything between runs.

  It does NOT verify that the declarations still PROVE what the row claims --
  that is the milestone corpus's job. It verifies only that they exist, which is
  exactly the failure mode that occurred and the one a text-level check can catch
  immediately."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]))

(def ledger-path "artifacts/or40/ahof-algorithm-ledger.edn")

(defn- source-files []
  (->> (file-seq (io/file "src/rainbow"))
       (filter #(string/ends-with? (.getName ^java.io.File %) ".clj"))))

(defn- declared-aliases
  "Every alias any module declares, read out of the `:name 'alias` spec fields."
  []
  (into #{}
        (mapcat (fn [file]
                  (map second
                       (re-seq #":name '([A-Za-z][A-Za-z0-9./*+!?<>=_-]*)"
                               (slurp file)))))
        (source-files)))

;; the ledger is written with namespaced map literals, so keys arrive as
;; :ahof/id, :ahof/specification and so on; match on the key NAME to stay
;; independent of which namespace the writer used
;; map keys in the ledger are not all Named -- some maps are keyed by content id
;; strings and by numbers -- so read the key name defensively
(defn- key-name [k]
  (when (instance? clojure.lang.Named k) (name k)))

(defn- has-key-named? [entry wanted]
  (some #(= wanted (key-name %)) (keys entry)))

(defn- ledger-entries []
  (->> (tree-seq coll? seq (edn/read-string (slurp ledger-path)))
       (filter map?)
       (filter #(and (has-key-named? % "id") (has-key-named? % "outcome")))))

(defn- entry-value [entry wanted]
  (some (fn [[k v]] (when (= wanted (key-name k)) v)) entry))

(defn- claimed-symbols
  "Alias symbols a proved row names as the declarations backing it."
  [entry]
  (->> [(entry-value entry "specification") (entry-value entry "package")]
       (remove nil?)
       (mapcat #(tree-seq coll? seq %))
       (filter symbol?)
       (filter #(some? (namespace %)))
       (into #{})))

(deftest every-proved-ledger-row-names-declarations-that-exist
  (let [entries (ledger-entries)
        proved (filter #(= :proved (entry-value % "outcome")) entries)
        declared (declared-aliases)]
    (testing "the ledger and the source were both readable"
      (is (seq entries) "no ledger entries were found")
      (is (seq proved) "no proved rows were found")
      (is (< 1000 (count declared))
          "declaration scan found implausibly few aliases"))
    (let [missing
          (into (sorted-map)
                (keep (fn [entry]
                        (let [absent (remove (comp declared str)
                                             (claimed-symbols entry))]
                          (when (seq absent)
                            [(entry-value entry "id")
                             (vec (sort (map str absent)))]))))
                proved)]
      (is (= {} missing)
          (str "these proved rows name declarations no module declares: "
               (pr-str missing))))))
