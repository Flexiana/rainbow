(ns rainbow.cli-options-test
  "Usage errors found by the nightly E2E of 2026-10-31 and 2026-11-01:

  - B-20261031-1: `lein verify` and `lein reproduce` read an unknown option (a misspelt
    `--checkpoint`, a trailing `--all`) as a namespace name, went on to check or rebuild the rest,
    and exited 1. An unknown option is a usage error: exit 2, the option named, nothing checked.
  - B-20261031-3: `lein show <alias> <namespace>` with a namespace that loads but is not a proof
    module printed a JVM NullPointerException message.
  - B-20261101-1: `lein share-bundle x x` (the input as the output) replaced the input and reported
    the output's size as the input's. It is refused, exit 2, and the input is kept."
  (:require [clojure.string :as string]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.main :as main]))

(defn- run
  "[exit code, printed text, what was started] of the command line `args`. Loading a checkpoint and
  rebuilding a milestone are recorded instead of done, so a usage error is seen to check nothing."
  [& args]
  (let [started (atom []) code (atom nil)
        text (with-redefs [checkpoint/load-checkpoint (fn [path]
                                                        (swap! started conj [:load-checkpoint path])
                                                        {:status :replayed :environment (environment/empty-environment)})
                           main/reproduce-milestone (fn [ns-sym]
                                                      (swap! started conj [:reproduce ns-sym])
                                                      {:namespace ns-sym :error "stubbed"})]
               (with-out-str (reset! code (main/run args))))]
    [@code text @started]))

(deftest an-unknown-option-is-a-usage-error-that-checks-nothing
  ;; B-20261031-1, E2E runs D12 and D35
  (doseq [[args problem]
          [[["verify" "--checkpiont" "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz" "rainbow.math.finite.rational-argmax"]
            "verify: unknown option --checkpiont"]
           [["verify" "rainbow.math.finite.rational-argmax" "--all"] "verify: unknown option --all"]
           [["verify" "--checkpoint" "c.edn.gz" "rainbow.math.finite.rational-argmax" "--checkpoint" "d.edn.gz"]
            "verify: --checkpoint given twice"]
           [["verify" "rainbow.math.finite.rational-argmax" "--bundle" "b.edn"]
            "verify: --bundle must be the first argument"]
           [["verify" "--bundle" "--reduction" "5" "b.edn"] "verify --bundle: unknown option --reduction"]
           [["verify" "--bundle" "b.edn" "--reductions" "5"] "verify --bundle: --reductions must come before the bundle files"]
           [["reproduce" "--all" "rainbow.milestones.ahof-bisection"]
            "reproduce: --all rebuilds every milestone; give either --all or milestone namespaces"]
           [["reproduce" "rainbow.milestones.ahof-bisection" "--all"]
            "reproduce: --all rebuilds every milestone; give either --all or milestone namespaces"]
           [["reproduce" "--al"] "reproduce: unknown option --al"]
           [["show" "nnrat/add-zero-right" "--modules" "rainbow.render"] "show: unknown option --modules"]]]
    (testing (pr-str args)
      (let [[code text started] (apply run args)]
        (is (= 2 code) text)
        (is (string/includes? text problem) text)
        (is (re-find #"(?m)^usage: lein " text) text)
        (is (not (re-find #"FAIL|Could not locate" text)) text)
        (is (empty? started) "a usage error checks and rebuilds nothing")))))

(deftest options-in-their-documented-places-still-work
  (testing "verify --checkpoint before the namespaces loads that checkpoint"
    (let [[code text started] (run "verify" "--checkpoint" "c.edn.gz" "clojure.string")]
      (is (= 1 code) text)
      (is (= [[:load-checkpoint "c.edn.gz"]] started))
      (is (re-find #"FAIL +clojure.string -- no extend-environment" text) text)))
  (testing "reproduce --all alone rebuilds every milestone"
    (with-redefs [main/reproducible-milestones (constantly ['rainbow.milestones.a 'rainbow.milestones.b])]
      (let [[code _ started] (run "reproduce" "--all")]
        (is (= 1 code))
        (is (= [[:reproduce 'rainbow.milestones.a] [:reproduce 'rainbow.milestones.b]] started))))))

(deftest show-names-a-namespace-that-is-not-a-proof-module
  ;; B-20261031-3, E2E run D31: printed `Cannot invoke "clojure.lang.IFn.invoke(Object)" ...`
  (let [[code text] (run "show" "nnrat/add-zero-right" "clojure.string")]
    (is (= 1 code) text)
    (is (re-find #"^FAIL show nnrat/add-zero-right -- clojure.string is not a proof module \(it defines no extend-environment\) -- Name the module that installs the declaration, such as rainbow.math.finite.rational-argmax" text) text)
    (is (not (re-find #"Cannot invoke|NullPointer|Execution error" text)) text)))

(deftest share-bundle-refuses-to-write-over-its-input
  ;; B-20261101-1, E2E runs D72 and D73
  (let [dir (.toFile (java.nio.file.Files/createTempDirectory "share-bundle-in-place" (make-array java.nio.file.attribute.FileAttribute 0)))
        in (java.io.File. dir "x.edn")
        content "{:rainbow.bundle/schema-version 1 :claims {} :declarations []}\n"
        link (java.io.File. dir "link.edn")]
    (try
      (spit in content)
      (java.nio.file.Files/createLink (.toPath link) (.toPath in))
      (doseq [[label out] [["the same path" (str in)]
                           ["the same file by another spelling" (str dir "/./x.edn")]
                           ["a hard link to the input" (str link)]]
              mode [[] ["--binary"] ["--plain"]]]
        (testing (str label " " (pr-str mode))
          (let [[code text] (apply run (concat ["share-bundle"] mode [(str in) out]))]
            (is (= 2 code) text)
            (is (string/includes? text (str "share-bundle: the output " out " is the input file " in)) text)
            (is (string/includes? text "Name a different output file") text)
            (is (re-find #"(?m)^usage: lein share-bundle" text) text)
            (is (= content (slurp in)) "the input is kept"))))
      (finally (.delete link) (.delete in) (.delete dir)))))
