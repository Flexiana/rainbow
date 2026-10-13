(ns rainbow.foreign.lean-export-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as string]
            [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.lean-round-trip :as lean-round-trip]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.foreign.lean-export :as lean-export]
            [rainbow.kernel :as kernel]))

(defn java-command [& arguments]
  (apply shell/sh
         (str (System/getProperty "java.home") "/bin/java")
         "-cp" (System/getProperty "java.class.path")
         "clojure.main" arguments))

(defn temporary-paths []
  (let [directory (.toFile (java.nio.file.Files/createTempDirectory
                            "rainbow-lean-roundtrip"
                            (make-array java.nio.file.attribute.FileAttribute 0)))
        source (io/file directory "RoundTrip.lean")
        fixture (io/file directory "neutral.edn")]
    {:source (.getAbsolutePath source)
     :fixture (.getAbsolutePath fixture)}))

(deftest checked-native-program-has-deterministic-structural-source
  (let [result (lean-round-trip/generated-export)]
    (is (= :exported (:status result)))
    (is (= "RainbowRoundTrip.functionComposition" (:lean/name result)))
    (is (= :definition (:lean/kind result)))
    (is (= {:rainbow :theorem :lean :definition
            :reason :lean-theorems-require-propositions}
           (:kind-adaptation result)))
    (is (= (slurp lean-round-trip/source-path) (:source result)))
    (is (= #{:sort :bound :const :app :pi :lam :let}
           (:constructors result)))))

(deftest proposition-remains-a-lean-theorem
  (let [result (lean-export/export-source
                (direct-term-corpus/build-environment) 'logic/implication-transitivity
                {:lean-name "implicationTransitivity"
                 :output-path "/tmp/rainbow-implication.edn"})]
    (is (= :exported (:status result)))
    (is (= :theorem (:lean/kind result)))
    (is (nil? (:kind-adaptation result)))
    (is (string/includes? (:source result)
                          "theorem implicationTransitivity"))))

(deftest supported-let-implicit-and-mapped-constant-forms-render
  (let [base (direct-term-corpus/build-environment)
        implicit-candidate
        {:rainbow/kind :definition
         :rainbow/aliases #{'export/implicit-let-identity}
         :rainbow/universes ['u]
         :rainbow/type [:pi [:sort [:param 'u]]
                        [:pi [:bound 0] [:bound 1] :implicit] :explicit]
         :rainbow/value [:lam [:sort [:param 'u]]
                         [:lam [:bound 0]
                          [:let [:bound 1] [:bound 0] [:bound 0]]
                          :implicit]
                         :explicit]
         :rainbow/transparency :reducible
         :rainbow/dependencies #{}
         :rainbow/schema-version 1}
        added (kernel/add-declaration base implicit-candidate)
        rendered (lean-export/export-source
                  (:environment added) 'export/implicit-let-identity
                  {:lean-name "implicitLetIdentity"
                   :output-path "/tmp/rainbow-implicit-let.edn"})
        nat-environment (lean/base-environment)
        nat-id (environment/resolve-id nat-environment 'data/Nat)
        nat-term [:const nat-id []]
        nat-candidate
        {:rainbow/kind :definition
         :rainbow/aliases #{'export/nat-identity}
         :rainbow/type [:pi nat-term nat-term :explicit]
         :rainbow/value [:lam nat-term [:bound 0] :explicit]
         :rainbow/transparency :reducible
         :rainbow/dependencies #{nat-id}
         :rainbow/schema-version 1}
        nat-added (kernel/add-declaration nat-environment nat-candidate)
        nat-rendered (lean-export/export-source
                      (:environment nat-added) 'export/nat-identity
                      {:lean-name "natIdentity"
                       :output-path "/tmp/rainbow-nat.edn"})]
    (is (= :accepted (:status added)))
    (is (= :exported (:status rendered)))
    (is (string/includes? (:source rendered) "{x1 : x0}"))
    (is (string/includes? (:source rendered) "let x2 : x0 := x1; x2"))
    (is (= :accepted (:status nat-added)))
    (is (= :exported (:status nat-rendered)))
    (is (string/includes? (:source nat-rendered) "Nat"))))

(deftest unchecked-forged-and-unmapped-inputs-reject-explicitly
  (let [base (direct-term-corpus/build-environment)
        unknown (lean-export/export-source
                 base 'missing/declaration
                 {:output-path "/tmp/missing.edn"})
        native-id (environment/resolve-id base 'logic/function-composition)
        native (environment/declaration base native-id)
        forged-environment
        (assoc-in base [:rainbow.environment/declarations native-id]
                  (assoc native :rainbow/value [:unsupported]))
        forged (lean-export/export-source
                forged-environment native-id {:output-path "/tmp/forged.edn"})
        wrapper-candidate
        {:rainbow/kind :theorem
         :rainbow/aliases #{'export/unmapped-wrapper}
         :rainbow/universes (:rainbow/universes native)
         :rainbow/type (:rainbow/type native)
         :rainbow/value [:const native-id [[:param 'u] [:param 'v] [:param 'w]]]
         :rainbow/transparency :opaque
         :rainbow/dependencies #{native-id}
         :rainbow/schema-version 1}
        wrapper (kernel/add-declaration base wrapper-candidate)
        unmapped (lean-export/export-source
                  (:environment wrapper) 'export/unmapped-wrapper
                  {:output-path "/tmp/unmapped.edn"})
        unsafe-name (lean-export/export-source
                     base 'logic/function-composition
                     {:lean-name "bad; #eval 1"
                      :output-path "/tmp/unsafe.edn"})]
    (is (= :lean-export/unknown-declaration
           (get-in unknown [:error :error/category])))
    (is (= :lean-export/forged-declaration
           (get-in forged [:error :error/category])))
    (is (= :accepted (:status wrapper)))
    (is (= :lean-export/unmapped-constant
           (get-in unmapped [:error :error/category])))
    (is (= :lean-export/unsafe-name
           (get-in unsafe-name [:error :error/category])))))

(deftest recorded-round-trip-is-exact-and-axiom-free
  (let [report (lean-round-trip/report)]
    (is (= :passed (:status report)))
    (is (= 'logic/function-composition (:selected-proof report)))
    (is (= {:type-exact? true :proof-exact? true :universes-exact? true
            :rainbow-before :checked :lean :accepted :rainbow-after :checked
            :axioms #{}}
           (:round-trip report)))
    (is (= {:distinct-statements-added 0 :kernel-checks 3
            :independent-checkers 2
            :round-tripped-declarations 1}
           (:proof-capacity report)))
    (is (= 1085 (:trusted-base-lines report)))))

(deftest pinned-lean-accepts-source-and-rejects-mutated-proof
  (if-not (.isFile (io/file lean-round-trip/default-lean-binary))
    (is true "Pinned Lean binary unavailable; deterministic recorded evidence still replays")
    (let [{valid-source :source valid-fixture :fixture} (temporary-paths)
          valid-export (lean-export/export-source
                        (direct-term-corpus/build-environment) lean-round-trip/selected-name
                        {:lean-namespace "RainbowRoundTrip"
                         :lean-name "functionComposition"
                         :output-path valid-fixture})
          _ (spit valid-source (:source valid-export))
          checked (lean-round-trip/check-with-lean lean-round-trip/default-lean-binary
                                         valid-source valid-fixture)
          {bad-source :source bad-fixture :fixture} (temporary-paths)
          bad-export (lean-export/export-source
                      (direct-term-corpus/build-environment) lean-round-trip/selected-name
                      {:lean-namespace "RainbowRoundTrip"
                       :lean-name "functionComposition"
                       :output-path bad-fixture})
          mutated (string/replace (:source bad-export)
                                  "(x3 (x4 x5))" "(x4 (x3 x5))")
          _ (spit bad-source mutated)
          rejected (lean-round-trip/check-with-lean lean-round-trip/default-lean-binary
                                          bad-source bad-fixture)]
      (is (= :accepted (:status checked)) (pr-str checked))
      (is (= lean/pinned-version (get-in checked [:toolchain :version])))
      (is (not= (:source bad-export) mutated))
      (is (= :rejected (:status rejected)))
      (is (= :lean-export/lean-rejected (:error/category rejected))))))

(deftest report-replays-and-is-deterministic-in-fresh-jvms
  (let [replay (java-command "-m" "rainbow.history.lean-round-trip" "replay" lean-round-trip/report-path)
        report-a (java-command "-m" "rainbow.history.lean-round-trip")
        report-b (java-command "-m" "rainbow.history.lean-round-trip")]
    (is (zero? (:exit replay)) (:err replay))
    (is (string/includes? (:out replay) ":status :replayed"))
    (is (zero? (:exit report-a)) (:err report-a))
    (is (zero? (:exit report-b)) (:err report-b))
    (is (= (:out report-a) (:out report-b)))))
