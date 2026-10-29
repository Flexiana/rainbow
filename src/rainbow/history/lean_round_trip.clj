(ns rainbow.history.lean-round-trip
  "Pinned Rainbow → Lean → Rainbow round trip for a native polymorphic program."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as string]
            [rainbow.canonical :as canonical]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.foreign.lean-export :as lean-export]
            [rainbow.kernel :as kernel]))

(def selected-name 'logic/function-composition)
(def lean-name "RainbowRoundTrip.functionComposition")
(def source-path "foreign/lean/RainbowRoundTrip.lean")
(def neutral-path "artifacts/day18/roundtrip-neutral.edn")
(def check-path "artifacts/day18/lean-check.edn")
(def report-path "artifacts/day18/report.edn")
(def default-lean-binary "/tmp/rainbow-lean-4.30.0/bin/lean")

(defn- selected-proof []
  (or (some #(when (= selected-name (:name %)) %) direct-term-corpus/proofs)
      (throw (ex-info "Selected Day-1 proof is missing" {:name selected-name}))))

(defn generated-export []
  (lean-export/export-source
   (direct-term-corpus/build-environment) selected-name
   {:lean-namespace "RainbowRoundTrip"
    :lean-name "functionComposition"
    :output-path neutral-path}))

(defn source-hash [source]
  (canonical/sha256 source))

(defn- check-record-base [source fixture]
  {:status :accepted
   :toolchain {:version lean/pinned-version :commit lean/pinned-commit}
   :source-hash (source-hash source)
   :fixture/id (canonical/content-id fixture)
   :lean/name lean-name})

(defn check-with-lean
  "Runs a generated source through the pinned Lean binary and records only
  deterministic evidence. The source itself selects the neutral output path."
  [binary lean-source-path fixture-path]
  (try
    (let [version-run (shell/sh binary "--version")
          version-output (str (:out version-run) (:err version-run))]
      (if-not (and (zero? (:exit version-run))
                   (string/includes? version-output lean/pinned-version)
                   (string/includes? version-output lean/pinned-commit))
        {:status :rejected :error/category :lean-export/toolchain-mismatch
         :exit (:exit version-run)}
        (let [check-run (shell/sh binary lean-source-path)]
          (if-not (zero? (:exit check-run))
            {:status :rejected :error/category :lean-export/lean-rejected
             :exit (:exit check-run) :stdout (:out check-run) :stderr (:err check-run)}
            (let [source (slurp lean-source-path)
                  fixture (lean/load-neutral fixture-path)
                  base (check-record-base source fixture)]
              ;; Lean writes the fixture even after an error; acceptance needs exit 0 and no sorryAx.
              (if (string/includes? (pr-str fixture) "sorryAx")
                {:status :rejected :error/category :lean-export/lean-rejected :reason :sorry-axiom}
                (assoc base :check/id (canonical/content-id base))))))))
    (catch java.io.IOException exception
      {:status :rejected :error/category :lean-export/tool-unavailable
       :message (.getMessage exception)})))

(defn- load-check []
  (edn/read-string (slurp check-path)))

(defn- replayed-check [source fixture]
  (try
    (let [recorded (load-check)
          expected-id (canonical/content-id (dissoc recorded :check/id))
          expected-base (check-record-base source fixture)]
      {:status (if (and (= :accepted (:status recorded))
                        (= expected-id (:check/id recorded))
                        (= expected-base (dissoc recorded :check/id)))
                 :replayed :rejected)
       :check/id (:check/id recorded)
       :expected/id expected-id
       :recorded recorded})
    (catch Throwable throwable
      {:status :rejected :error/category :lean-export/check-read-failed
       :message (.getMessage throwable)})))

(defn round-trip []
  (try
    (let [native-environment (direct-term-corpus/build-environment)
          native-id (environment/resolve-id native-environment selected-name)
          native (environment/declaration native-environment native-id)
          proof (selected-proof)
          exported (generated-export)
          checked-source (slurp source-path)
          source-match? (= checked-source (:source exported))
          fixture (lean/load-neutral neutral-path)
          check-replay (replayed-check checked-source fixture)
          imported (lean/import-fixture (environment/empty-environment) fixture)
          object (first (:objects imported))
          returned-id (:foreign/native-declaration-id object)
          returned (when returned-id
                     (environment/declaration (:environment imported) returned-id))
          native-check (kernel/check native-environment
                                     (:rainbow/value native)
                                     (:rainbow/type native)
                                     (set (:rainbow/universes native)))
          returned-check (when returned
                           (kernel/check (:environment imported)
                                         (:rainbow/value returned)
                                         (:rainbow/type returned)
                                         (set (:rainbow/universes returned))))]
      {:native-environment native-environment
       :native native
       :proof proof
       :export exported
       :source checked-source
       :source-match? source-match?
       :fixture fixture
       :check-replay check-replay
       :import imported
       :foreign-object object
       :returned returned
       :native-check native-check
       :returned-check returned-check})
    (catch Throwable throwable
      {:status :rejected :error/category :lean-export/round-trip-failed
       :message (.getMessage throwable)})))

(defn report []
  (let [{:keys [native proof export source source-match? fixture check-replay import
                foreign-object returned native-check returned-check]
         :as result} (round-trip)]
    (if (= :rejected (:status result))
      result
      (let [type-match? (= (:rainbow/type native) (:rainbow/type returned))
            proof-match? (= (:rainbow/value native) (:rainbow/value returned))
            universes-match? (= (:rainbow/universes native)
                                (:rainbow/universes returned))
            passed? (and (= :exported (:status export))
                         source-match?
                         (= :replayed (:status check-replay))
                         (= :imported (:status import))
                         (= lean-name (:foreign/name foreign-object))
                         (= :definition (:foreign/kind foreign-object))
                         (= :checked (:status native-check))
                         (= :checked (:status returned-check))
                         type-match? proof-match? universes-match?
                         (= #{} (kernel/axioms (:environment import)
                                              (:rainbow/id returned))))
            base
            {:status (if passed? :passed :failed)
             :selected-proof selected-name
             :native-declaration-id (:rainbow/id native)
             :lean/name lean-name
             :kind-adaptation (:kind-adaptation export)
             :toolchain {:version lean/pinned-version :commit lean/pinned-commit}
             :source-hash (source-hash source)
             :fixture/id (canonical/content-id fixture)
             :check/id (:check/id check-replay)
             :round-trip {:type-exact? type-match?
                          :proof-exact? proof-match?
                          :universes-exact? universes-match?
                          :rainbow-before (:status native-check)
                          :lean :accepted
                          :rainbow-after (:status returned-check)
                          :axioms (kernel/axioms (:environment import)
                                                (:rainbow/id returned))}
             :proof-capacity {:distinct-statements-added 0
                              :kernel-checks 3
                              :independent-checkers 2
                              :round-tripped-declarations 1}
             :trusted-base-lines 1085}]
        (assoc base :report/id (canonical/content-id base))))))

(defn save-edn! [path value]
  (io/make-parents path)
  (spit path (str (pr-str value) "\n"))
  value)

(defn record!
  ([] (record! default-lean-binary))
  ([binary]
   (let [exported (generated-export)
         checked-source (slurp source-path)]
     (when-not (= :exported (:status exported))
       (throw (ex-info "Rainbow export rejected" {:export exported})))
     (when-not (= checked-source (:source exported))
       (throw (ex-info "Checked-in Lean source differs from deterministic export"
                       {:expected-hash (source-hash (:source exported))
                        :actual-hash (source-hash checked-source)})))
     (let [check (check-with-lean binary source-path neutral-path)]
       (when-not (= :accepted (:status check))
         (throw (ex-info "Pinned Lean rejected the generated declaration"
                         {:check check})))
       (save-edn! check-path check)
       (let [value (report)]
         (when-not (= :passed (:status value))
           (throw (ex-info "Recorded round trip failed" {:report value})))
         (save-edn! report-path value)
         {:status :recorded :check/id (:check/id check)
          :report/id (:report/id value)})))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (and (= :passed (:status value)) (= expected (:report/id value)))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :lean-export/report-id-mismatch
         :expected expected :actual (:report/id value)}))
    (catch Throwable throwable
      {:status :rejected :error/category :lean-export/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command argument]]
  (case command
    "record" (println (pr-str (record! (or argument default-lean-binary))))
    "replay" (let [result (load-report (or argument report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
