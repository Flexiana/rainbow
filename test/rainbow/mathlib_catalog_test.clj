(ns rainbow.mathlib-catalog-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.history.mathlib-hidden-batch-1 :as mathlib-hidden-batch-1]
            [rainbow.history.mathlib-catalog-baseline :as mathlib-catalog-baseline]
            [rainbow.foreign.mathlib :as mathlib])
  (:import (java.io FileOutputStream OutputStreamWriter)
           (java.util.zip GZIPOutputStream)))

(def header
  {:rainbow.catalog/kind :header
   :foreign/system :lean
   :foreign/library :mathlib
   :foreign/version mathlib/pinned-version
   :foreign/commit mathlib/pinned-commit
   :foreign/proofs :redacted
   :foreign/statement-representation :lean-hash64-profile
   :foreign/schema-version 2})

(def declarations
  [{:rainbow.catalog/kind :declaration
    :foreign/name "Example.explicit"
    :foreign/kind :theorem
    :foreign/module "Mathlib.Example"
    :foreign/universes []
    :foreign/type-fingerprint "lean-hash64:1"
    :foreign/type-profile {:nodes 5 :strict-implicit? false
                           :instance-implicit? false :literal? false
                           :metavariable? false :free-variable? false
                           :projection? false :level-metavariable? false}
    :foreign/value :redacted
    :foreign/unsafe? false
    :foreign/public? true}
   {:rainbow.catalog/kind :declaration
    :foreign/name "Example.instance"
    :foreign/kind :theorem
    :foreign/module "Mathlib.Example"
    :foreign/universes []
    :foreign/type-fingerprint "lean-hash64:2"
    :foreign/type-profile {:nodes 6 :strict-implicit? false
                           :instance-implicit? true :literal? false
                           :metavariable? false :free-variable? false
                           :projection? true :level-metavariable? false}
    :foreign/value :redacted
    :foreign/unsafe? false
    :foreign/public? true}
   {:rainbow.catalog/kind :declaration
    :foreign/name "Example.definition"
    :foreign/kind :definition
    :foreign/module "Mathlib.Other"
    :foreign/universes []
    :foreign/type-fingerprint "lean-hash64:3"
    :foreign/type-profile {:nodes 3 :strict-implicit? false
                           :instance-implicit? false :literal? false
                           :metavariable? false :free-variable? false
                           :projection? false :level-metavariable? false}
    :foreign/value :redacted
    :foreign/unsafe? true
    :foreign/public? true}])

(defn- with-catalog [forms function]
  (let [file (java.io.File/createTempFile "rainbow-mathlib-catalog-" ".edn")]
    (try
      (spit file (str (clojure.string/join "\n" (map pr-str forms)) "\n"))
      (function (.getAbsolutePath file))
      (finally
        (.delete file)))))

(defn- with-gzip-catalog [forms function]
  (let [file (java.io.File/createTempFile "rainbow-mathlib-catalog-" ".edn.gz")]
    (try
      (with-open [writer (OutputStreamWriter.
                          (GZIPOutputStream. (FileOutputStream. file)) "UTF-8")]
        (.write writer (str (clojure.string/join "\n" (map pr-str forms)) "\n")))
      (function (.getAbsolutePath file))
      (finally
        (.delete file)))))

(deftest streams-and-summarizes-proof-redacted-catalog
  (with-catalog
    (cons header declarations)
    (fn [path]
      (let [summary (mathlib/summarize path #{"Example.explicit"})]
        (is (= 3 (:declarations summary)))
        (is (= 2 (:theorems summary)))
        (is (= 2 (:public-theorems summary)))
        (is (= 0 (:private-theorems summary)))
        (is (= 1 (:proved summary)))
        (is (= 1/2 (get-in summary [:coverage :ratio])))
        (is (= 1 (:structural-fragment-theorems summary)))
        (is (= {:instance-implicit 1} (:unsupported-binders summary)))
        (is (= {:unsupported 1} (:unsupported-operators summary)))
        (is (= {:projection 1} (:unsupported-features summary)))
        (is (= {"Mathlib.Example" 2} (:theorem-module-counts summary)))
        (is (= 2 (:modules summary)))
        (is (= 1 (:unsafe summary)))
        (is (string? (:catalog/id summary)))))))

(deftest rejects-unpinned-or-proof-bearing-catalogs
  (testing "proof visibility is part of the catalog trust boundary"
    (with-catalog
      [(assoc header :foreign/proofs :included)]
      (fn [path]
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo
             #"proof-redacted Mathlib"
             (mathlib/reduce-catalog path nil (fn [state _] state)))))))
  (testing "a redacted header cannot conceal a proof-bearing declaration"
    (with-catalog
      [header (assoc (first declarations) :foreign/value [:proof :body])]
      (fn [path]
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo
             #"declaration is not proof-redacted"
             (mathlib/reduce-catalog path nil (fn [state _] state))))))))

(deftest declaration-identity-excludes-redacted-value-and-location
  (let [declaration (first declarations)]
    (is (= (mathlib/declaration-id declaration)
           (mathlib/declaration-id
            (assoc declaration
                   :foreign/value [:forbidden :proof]
                   :foreign/location {:line 99}))))
    (is (not= (mathlib/declaration-id declaration)
              (mathlib/declaration-id
               (assoc declaration :foreign/type-fingerprint "lean-hash64:changed"))))))

(deftest gzip-is-transparent-to-streaming-and-content-identity
  (let [forms (cons header declarations)]
    (with-catalog
      forms
      (fn [plain-path]
        (with-gzip-catalog
          forms
          (fn [gzip-path]
            (is (= (mathlib/file-sha256 plain-path)
                   (mathlib/file-sha256 gzip-path)))
            (is (= (mathlib/summarize plain-path #{})
                   (mathlib/summarize gzip-path #{})))))))))

(deftest coverage-report-uses-the-compiled-theorem-denominator
  (let [proved-names (mapv :foreign/name mathlib-hidden-batch-1/theorem-specs)
        theorem (fn [name]
                  {:rainbow.catalog/kind :declaration
                   :foreign/name name
                   :foreign/kind :theorem
                   :foreign/module "Mathlib.Example"
                   :foreign/universes []
                   :foreign/type-fingerprint (str "lean-hash64:" name)
                   :foreign/type-profile {:nodes 2 :strict-implicit? false
                                          :instance-implicit? false
                                          :literal? false :metavariable? false
                                          :free-variable? false :projection? false
                                          :level-metavariable? false}
                   :foreign/value :redacted
                   :foreign/unsafe? false
                   :foreign/public? true})]
    (with-catalog
      (cons header (map theorem (conj proved-names "Example.unproved")))
      (fn [path]
        (let [report (mathlib-catalog-baseline/report path)]
          (is (= :passed (:status report)))
          (is (= 5 (get-in report [:coverage :independently-proved])))
          (is (= 6 (get-in report [:coverage :theorem-declarations])))
          (is (= 5/6 (get-in report [:coverage :ratio])))
          (is (= 250/3 (get-in report [:coverage :percent])))
          (is (= ["Example.unproved"]
                 (mapv :foreign/name
                       (get-in report [:curriculum-signals
                                       :smallest-unproved-structural-candidates]))))
          (is (false? (get-in report [:method
                                      :source-text-regex-used-as-denominator?])))
          (is (= :none (:trusted-base-change report))))))))

(deftest bounded-statements-must-match-the-compact-ledger
  (let [declaration (first declarations)
        name (:foreign/name declaration)
        statement-header
        {:rainbow.catalog/kind :header
         :foreign/system :lean :foreign/library :mathlib
         :foreign/version mathlib/pinned-version
         :foreign/commit mathlib/pinned-commit
         :foreign/proofs :redacted :foreign/selection :bounded
         :foreign/schema-version 1}
        statement {:rainbow.catalog/kind :statement
                   :foreign/name name
                   :foreign/module (:foreign/module declaration)
                   :foreign/type-fingerprint (:foreign/type-fingerprint declaration)
                   :foreign/type [:sort [:zero]]
                   :foreign/value :redacted}]
    (with-catalog
      (cons header declarations)
      (fn [catalog-path]
        (with-catalog
          [statement-header statement]
          (fn [statement-path]
            (let [result (mathlib/verify-statement-batch
                          catalog-path statement-path #{name})]
              (is (= :verified (:status result)))
              (is (= 1 (count (:statements result)))))))))))

(deftest bounded-statement-dependencies-rank-nativeization-readiness
  (let [statements
        [{:foreign/name "Example.ready"
          :foreign/type
          [:app [:const "And" []]
           [:app [:const "Known" []] [:const "Known" []]]]}
         {:foreign/name "Example.blocked"
          :foreign/type
          [:app [:const "Opaque" []] [:const "Known" []]]}]
        audit (mathlib/audit-statement-dependencies
               statements #{"And" "Known"})]
    (is (= 2 (:statement-count audit)))
    (is (= 1 (:fully-nativeizable audit)))
    (is (= 1 (:with-unresolved audit)))
    (is (= {"Opaque" 1} (:unresolved-constant-counts audit)))
    (is (= ["And" "Known"]
           (get-in audit [:statements 0 :foreign/constants])))
    (is (true? (get-in audit [:statements 0 :fully-nativeizable?])))
    (is (= ["Opaque"] (get-in audit [:statements 1 :unresolved])))))

(deftest study-curriculum-is-proof-redacted-bounded-and-order-invariant
  (let [eligible (mapv (fn [index]
                         (assoc (first declarations)
                                :foreign/name (str "Logic.theorem" index)
                                :foreign/module "Mathlib.Logic.Basic"
                                :foreign/type-fingerprint (str "lean-hash64:" index)
                                :foreign/type-profile
                                (assoc (:foreign/type-profile (first declarations))
                                       :nodes (+ 2 (mod index 3)))))
                       (range 20))
        options {:target-count 10 :maximum-type-nodes 10}]
    (with-catalog
      (cons header eligible)
      (fn [forward-path]
        (with-catalog
          (cons header (reverse eligible))
          (fn [reverse-path]
            (let [forward (mathlib/select-study-curriculum forward-path options)
                  reverse (mathlib/select-study-curriculum reverse-path options)]
              (is (= (:study/targets forward) (:study/targets reverse)))
              (is (= 10 (count (:study/targets forward))))
              (is (= {:development 8 :held-out 1 :transfer 1}
                     (:study/partition-counts forward)))
              (is (every? #(not (contains? % :foreign/value))
                          (:study/targets forward))))))))))
