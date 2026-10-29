(ns rainbow.share-bundle-errors-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.main :as main]))

(deftest unreadable-bundles-are-actionable-cli-failures
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "bundle-errors" (make-array java.nio.file.attribute.FileAttribute 0)))
        missing (java.io.File. dir "missing.edn")
        truncated (java.io.File. dir "truncated.edn")
        out (java.io.File. dir "out.edn")]
    (try
      (spit truncated "{:claims {")
      (doseq [input [missing truncated]]
        (let [result (atom nil)
              text (with-out-str (reset! result (#'main/share-bundle-main [(str input) (str out)])))]
          (is (false? @result))
          (is (re-find #"FAIL share-bundle" text))
          (is (.contains text (str input)))
          (is (re-find #"[Cc]heck" text))
          (is (not (.exists out)))
          (is (not (re-find #"Execution error|Full report at" text)))))
      (finally (.delete truncated) (.delete out) (.delete dir)))))
