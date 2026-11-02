(ns rainbow.cli-locale-test
  "The command line prints numbers the same in every locale (B-20261028-7): on a cs or pt default
  locale share-bundle printed `22 141 527 bytes` and verify --bundle `(10,8 s)`, while
  doc/bundles.md shows `2,363,278 bytes`."
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.environment :as environment]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.main :as main]))

(defn- in-locale [^java.util.Locale locale f]
  (let [saved (java.util.Locale/getDefault)]
    (try (java.util.Locale/setDefault locale) (f)
         (finally (java.util.Locale/setDefault saved)))))

(deftest numbers-do-not-follow-the-default-locale
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "cli-locale" (make-array java.nio.file.attribute.FileAttribute 0)))
        in (java.io.File. dir "in.edn") out (java.io.File. dir "out.edn")
        bundle (main/proof-bundle {:checkpoint "test-base" :modules [] :base-env (environment/empty-environment)
                                   :env (corpus/build-environment) :claims (map :name corpus/proofs)})]
    (try
      (main/write-bundle! (str in) bundle)
      (is (< 1000 (.length in)) "large enough for a thousands separator")
      (doseq [locale [(java.util.Locale/forLanguageTag "cs-CZ") (java.util.Locale/forLanguageTag "pt-BR")
                      (java.util.Locale/forLanguageTag "de-DE") (java.util.Locale/forLanguageTag "ar-EG")]]
        (testing (str locale)
          (let [text (in-locale locale #(with-out-str (#'main/share-bundle-main [(str in) (str out)])))]
            (is (re-find #"\(\d{1,3}(,\d{3})+ bytes\) -> " text) text)
            (is (.contains text (String/format java.util.Locale/ROOT "(%,d bytes)" (to-array [(.length in)]))) text))
          (let [text (in-locale locale #(with-out-str (#'main/verify-bundles-main [(str (java.io.File. dir "missing.edn"))])))]
            (is (re-find #"\(\d+\.\d s\)" text) text))))
      (finally (.delete in) (.delete out) (.delete dir)))))
