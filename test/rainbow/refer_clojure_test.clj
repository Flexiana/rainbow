(ns rainbow.refer-clojure-test
  "No namespace under src/ prints `WARNING: disj already refers to: #'clojure.core/disj` when it loads
  (B-20261028-6, B-20261030-9): a namespace that defines a var named like a clojure.core var it refers
  must exclude that var with (:refer-clojure :exclude [..]); otherwise Clojure prints the warning to
  stderr, and lein verify, show and lp-view print it with their output. The check reads the source
  text, so it holds whatever was loaded before it in the same JVM (a reload never repeats the
  warning). It covers every clojure.core public name in every src namespace."
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [clojure.test :refer [deftest is]]))

(def checked
  "The clojure.core names checked in every namespace: all of clojure.core's public vars."
  (set (map str (keys (ns-publics 'clojure.core)))))

(defn- ns-form [^java.io.File f]
  (with-open [r (java.io.PushbackReader. (io/reader f))]
    (binding [*read-eval* false]
      (let [form (read {:eof nil :read-cond :allow} r)]
        (when (and (seq? form) (= 'ns (first form))) form)))))

(defn- excluded
  "A predicate on the clojure.core names a ns form keeps out: its :exclude, or all but its :only."
  [form]
  (let [clause (first (filter #(and (seq? %) (= :refer-clojure (first %))) form))
        opts (apply hash-map (rest clause))]
    (if-let [only (:only opts)]
      (complement (set (map str only)))
      (set (map str (:exclude opts))))))

(def ^:private top-level-def
  #"(?m)^\((?:def|defn|defn-|defmacro|defonce|defmulti|definline|defprotocol|defrecord|deftype)\s+(?:\^\S+\s+)*([^\s\[\]()]+)")

(defn shadowing
  "{file [names]}: the checked clojure.core names each src namespace defines without excluding them."
  []
  (into (sorted-map)
        (for [^java.io.File f (file-seq (io/file "src")) :when (string/ends-with? (.getName f) ".clj")
              :let [form (ns-form f) ex (some-> form excluded)
                    defined (set (map second (re-seq top-level-def (slurp f))))
                    bad (when form (sort (remove ex (filter checked defined))))]
              :when (seq bad)]
          [(str f) (vec bad)])))

(deftest no-namespace-shadows-a-clojure-core-var
  (is (< 100 (count (filter #(string/ends-with? (.getName ^java.io.File %) ".clj") (file-seq (io/file "src")))))
      "run from the project directory")
  (is (= {} (shadowing))))

(deftest the-check-sees-a-shadowing-definition
  ;; the lever: a namespace that defines disj without excluding it is reported, one that excludes it is not
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "refer-clojure" (make-array java.nio.file.attribute.FileAttribute 0)))
        bad (io/file dir "bad.clj") good (io/file dir "good.clj")]
    (try
      (spit bad "(ns x.bad\n  (:require [clojure.string :as s]))\n\n(def disj 1)\n(defn- ^:private update [] 2)\n")
      (spit good "(ns x.good\n  (:refer-clojure :exclude [disj])\n  (:require [clojure.string :as s]))\n\n(def disj 1)\n")
      (let [defined #(set (map second (re-seq top-level-def (slurp %))))]
        (is (= #{"disj" "update"} (set (remove (excluded (ns-form bad)) (filter checked (defined bad))))))
        (is (empty? (remove (excluded (ns-form good)) (filter checked (defined good))))))
      (finally (.delete bad) (.delete good) (.delete dir)))))
