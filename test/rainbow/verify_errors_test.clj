(ns rainbow.verify-errors-test
  "lein verify says what to do for the common mistakes (B-20261028-4): a missing or truncated bundle
  file, a --reductions value that is not a number, and a namespace that does not exist or is not a
  proof module."
  (:require [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.environment :as environment]
            [rainbow.main :as main]))

(defn- verify-bundles [& args]
  (let [result (atom nil) text (with-out-str (reset! result (#'main/verify-bundles-main args)))] [@result text]))

(defn- raw? [text] (re-find #"Execution error|Full report at|For input string|NoSuchFileException" text))

(deftest bundle-file-errors-say-what-to-check
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "verify-errors" (make-array java.nio.file.attribute.FileAttribute 0)))
        missing (str (java.io.File. dir "does-not-exist.edn"))
        truncated (java.io.File. dir "truncated.edn")]
    (try
      (spit truncated "{:rainbow.bundle/schema-version 1 :claims {")
      (testing "a missing file: the reason, not only its path"
        (let [[ok text] (verify-bundles missing)]
          (is (false? ok))
          (is (re-find #"FAIL +\S+does-not-exist\.edn -- no such file -- Check the path of the bundle file" text) text)
          (is (not (raw? text)) text)))
      (testing "a truncated file: not readable, and what to check"
        (let [[ok text] (verify-bundles (str truncated))]
          (is (false? ok))
          (is (re-find #"not readable as a proof bundle: EOF while reading.* -- Check that the file is complete" text) text)
          (is (not (raw? text)) text)))
      (testing "a directory"
        (let [[ok text] (verify-bundles (str dir))]
          (is (false? ok))
          (is (re-find #"is a directory, not a bundle file -- Name the bundle file" text) text)))
      (finally (.delete truncated) (.delete dir)))))

(deftest a-reductions-value-that-is-not-a-number-is-named
  (doseq [args [["--reductions" "abc" "b.edn"] ["--reductions" "-5" "b.edn"] ["--reductions"]]]
    (let [[ok text] (apply verify-bundles args)]
      (is (not (true? ok)))
      (is (re-find #"--reductions needs a positive whole number" text) text)
      (is (string/includes? text "usage: lein verify --bundle [--reductions N] <bundle> ...") text)
      (is (not (re-find #"FAIL" text)) text)
      (is (not (raw? text)) text))))

(deftest namespace-errors-say-what-to-check
  (let [base (environment/empty-environment)]
    (testing "an unknown namespace: no stray {} after the message, and what to check"
      (let [{:keys [error]} (main/verify-namespace base 'rainbow.no.such.namespace)]
        (is (re-find #"Could not locate rainbow/no/such/namespace" error))
        (is (not (re-find #"\{\}" error)) error)
        (is (re-find #"-- Check the namespace name" error) error)))
    (testing "a namespace that is not a proof module names what to give instead"
      (let [{:keys [error]} (main/verify-namespace base 'clojure.string)]
        (is (re-find #"not a proof module\) -- Name a proof module" error) error)))))
