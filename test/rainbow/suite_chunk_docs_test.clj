(ns rainbow.suite-chunk-docs-test
  "The documented chunk size of scripts/run-suite-chunked.sh is the script's own default (B-20261031-4:
  CONTRIBUTING.md said 40 namespaces per JVM, while twenty proof environments in one JVM had already
  exhausted a 5 GB heap and the script defaults to five)."
  (:require [clojure.test :refer [deftest is testing]]))

(defn- script-default []
  (some->> (slurp "scripts/run-suite-chunked.sh") (re-find #"chunk_size=\"\$\{1:-(\d+)\}\"") second parse-long))

(deftest every-documented-chunk-size-is-the-default
  (let [default (script-default)]
    (is (= 5 default) "the script's default chunk size")
    (doseq [doc ["CONTRIBUTING.md" "README.md"]]
      (testing doc
        (let [sizes (map (comp parse-long second) (re-seq #"run-suite-chunked\.sh (\d+)" (slurp doc)))]
          (is (seq sizes) "the document names a chunk size")
          (is (every? #{default} sizes) (pr-str sizes)))))))
