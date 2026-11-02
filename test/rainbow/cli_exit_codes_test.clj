(ns rainbow.cli-exit-codes-test
  "Every command exits 2 on a usage error and 1 on a failed check or refused input (B-20261028-5):
  share-bundle, show and verify --bundle with no arguments exited 1, the code of a failed check, and
  verify --bundle prefixed its usage line with `FAIL --`."
  (:require [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.main :as main]))

(defn- run [& args]
  (let [code (atom nil) text (with-out-str (reset! code (main/run args)))] [@code text]))

(deftest usage-errors-exit-2-and-print-the-usage-line
  (doseq [args [[] ["no-such-command"]
                ["verify"] ["verify" "--checkpoint"] ["verify" "--checkpoint" "c.edn.gz"]
                ["verify" "--bundle"] ["verify" "--bundle" "--reductions" "abc" "b.edn"] ["verify" "--bundle" "--reductions"]
                ["share-bundle"] ["share-bundle" "in.edn"] ["share-bundle" "--binary" "in.edn"] ["share-bundle" "a" "b" "c"]
                ["share-bundle" "--binry" "in.edn" "out.edn"]
                ["show"]
                ["reproduce"]]]
    (testing (pr-str args)
      (let [[code text] (apply run args)]
        (is (= 2 code) text)
        (is (re-find #"(?m)^usage: lein " text) text)
        (is (not (re-find #"FAIL" text)) text)))))

(deftest failed-checks-exit-1
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "exit-codes" (make-array java.nio.file.attribute.FileAttribute 0)))
        missing (str (java.io.File. dir "missing.edn"))]
    (try
      (doseq [args [["verify" "--bundle" missing]
                    ["share-bundle" missing (str (java.io.File. dir "out.edn"))]
                    ["verify" "--checkpoint" (str (java.io.File. dir "no-checkpoint.edn.gz")) "rainbow.no.such.namespace"]]]
        (testing (pr-str args)
          (let [[code text] (apply run args)]
            (is (= 1 code) text)
            (is (re-find #"FAIL" text) text)
            (is (not (string/includes? text "usage:")) text))))
      (finally (.delete dir)))))

(deftest exit-code-of-a-result
  (is (= [0 1 1 2] (map main/exit-code [true false nil :usage]))))
