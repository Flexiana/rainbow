(ns rainbow.foreign.lean-export-test
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as string]
            [clojure.test :refer :all]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.history.lean-round-trip :as lean-round-trip]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.foreign.lean :as lean]
            [rainbow.foreign.lean-export :as lean-export]
            [rainbow.kernel :as kernel]
            [rainbow.math.profile :as profile]
            [rainbow.math.logic.proposition :as proposition]))

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

;; ---- closures with inductive blocks and logical principles -------------------------------------------

(def checkpoint
  (delay (let [loaded (checkpoint/load-checkpoint "artifacts/ahof/d63-eligibility-traces/checkpoint.edn.gz")]
           (when-not (= :replayed (:status loaded)) (throw (ex-info "Checkpoint rejected" {})))
           (:environment loaded))))

;; Any Lean 4 binary (RAINBOW_LEAN); the closure files need no Lean library, only the prelude.
(def lean-binary (or (System/getenv "RAINBOW_LEAN") lean-round-trip/default-lean-binary))

(defn run-lean [source]
  (let [file (java.io.File/createTempFile "rainbow-closure" ".lean")]
    (spit file source)
    (let [run (shell/sh lean-binary (.getAbsolutePath file))] (assoc run :log (str (:out run) (:err run))))))

(defn axioms-line [log name]
  (some #(when (string/starts-with? % (str "'" name "'")) %) (string/split-lines (string/replace log #",\n\s*" ", "))))

(deftest non-ascii-universe-names-are-escaped-and-implicit-arguments-passed
  (let [base (direct-term-corpus/build-environment)
        identity-at (fn [u] {:rainbow/kind :definition :rainbow/aliases #{'export/implicit-identity}
                             :rainbow/universes [u]
                             :rainbow/type [:pi [:sort [:param u]] [:pi [:bound 0] [:bound 1] :explicit] :implicit]
                             :rainbow/value [:lam [:sort [:param u]] [:lam [:bound 0] [:bound 0] :explicit] :implicit]
                             :rainbow/transparency :reducible :rainbow/dependencies #{} :rainbow/schema-version 1})
        identity (identity-at 'u₁)
        added (:environment (kernel/add-declaration base identity))
        id (environment/resolve-id added 'export/implicit-identity)
        user {:rainbow/kind :definition :rainbow/aliases #{'export/implicit-user}
              :rainbow/universes ['v]
              :rainbow/type [:pi [:sort [:param 'v]] [:pi [:bound 0] [:bound 1] :explicit] :explicit]
              :rainbow/value [:lam [:sort [:param 'v]]
                              [:lam [:bound 0] [:app [:app [:const id [[:param 'v]]] [:bound 1]] [:bound 0]]
                               :explicit] :explicit]
              :rainbow/transparency :reducible :rainbow/dependencies #{id} :rainbow/schema-version 1}
        both (:environment (kernel/add-declaration added user))
        single (lean-export/export-source added 'export/implicit-identity
                                          {:lean-name "implicitIdentity" :output-path "/tmp/rainbow-u1.edn"})
        closure (lean-export/export-closure both 'export/implicit-user {})
        bad (lean-export/export-source (:environment (kernel/add-declaration base (identity-at (symbol "u»"))))
                                       'export/implicit-identity {:output-path "/tmp/rainbow-bad.edn"})]
    (is (= :exported (:status single)))
    (is (string/includes? (:source single) "def implicitIdentity.{«u₁»}"))
    (is (string/includes? (:source single) "(Sort «u₁»)"))
    (is (= :exported (:status closure)))
    (is (re-find #"\(@RainbowXcheck\.export_implicit_identity_\w+\.\{v\} x0 x1\)" (:source closure)))
    (is (= :lean-export/unsafe-universe-name (get-in bad [:error :error/category])))
    (when (.isFile (io/file lean-binary))
      (let [run (run-lean (:source closure))]
        (is (zero? (:exit run)) (:log run))
        (is (string/includes? (:log run) "does not depend on any axioms"))))))

(deftest closures-map-nat-natively-and-assert-every-generated-type
  (let [result (lean-export/export-closure @checkpoint 'nat/multiply-successor-right {})
        blocks (filter #(contains? % :native?) (:units result))]
    (is (= :exported (:status result)))
    (is (= [{:alias 'data/Nat :lean/name "Nat" :native? true :prop? false :prop-only-elimination? false :copy nil}] blocks))
    (is (string/includes? (:source result) "noncomputable def data_Nat_3506a443.rainbowCheckRec.{_rainbow_motive_universe}"))
    (is (string/includes? (:source result) ":=\n  @Nat.rec.{_rainbow_motive_universe}\n"))
    (is (not (string/includes? (:source result) "\naxiom ")))
    (when (.isFile (io/file lean-binary))
      (let [run (run-lean (:source result))]
        (is (zero? (:exit run)) (:log run))
        (is (string/includes? (:log run) "does not depend on any axioms"))))))

(deftest blocks-whose-sort-may-be-prop-are-split-into-prop-and-type-copies
  ;; Lean refuses Rainbow's List at Sort u (Prop for u = 0 only), so each block and each unit using one is
  ;; exported as copies at u := 0 and u := u + 1, each with Rainbow's exact types asserted.
  (let [[lists product append mapped] (for [a '[data/List.rec data/Product.rec list/append list/map]]
                                     (lean-export/export-closure @checkpoint a {}))
        copies (fn [result alias] (mapv (juxt :copy :prop? :prop-only-elimination?)
                                        (filter #(= alias (:alias %)) (:units result))))]
    (is (= [:exported :exported :exported :exported] (map :status [lists product append mapped])))
    (is (= [["_U0" true true] ["_Us" false false]] (copies lists 'data/List)))
    (is (= [["_U00" true false] ["_U0s" false false] ["_Usx" false false]] (copies product 'data/Product)))
    (is (re-find #"inductive data_List_\w+_U0 \(x0 : \(Sort 0\)\) : \(Sort 0\) where" (:source lists)))
    (is (re-find #"inductive data_List_\w+_Us\.\{u\} \(x0 : \(Sort \(u \+ 1\)\)\) : \(Sort \(u \+ 1\)\) where" (:source lists)))
    (is (= 2 (count (re-seq #"rainbowCheckType" (:source lists)))) "Rainbow's exact type is asserted for both copies")
    (is (re-find #":=\n  @RainbowXcheck\.data_List_\w+_U0\.rec\n" (:source lists)) "Prop copy: no motive universe")
    (is (= ["_Us"] (map :copy (filter #(= 'list/append (:alias %)) (:units append)))))
    (is (some #{{:alias 'list/append :copy "_U0"}} (:dropped-copies append)) "Rainbow requires u >= 1 for list/append")
    (is (= ["_Us0" "_Uss"] (map #(re-find #"_U\w+$" %) (:lean/names mapped))))
    (when (.isFile (io/file lean-binary))
      (doseq [result [lists product append mapped]]
        (let [run (run-lean (:source result))]
          (is (zero? (:exit run)) (:log run))
          (is (not (string/includes? (:log run) "sorryAx")))))
      (let [exact (run-lean "inductive L.{u} (x0 : Sort u) : Sort u where\n  | nil : L x0\n")]
        (is (not (zero? (:exit exact))))
        (is (string/includes? (:log exact) "it may be `Prop` for some parameter values"))))))

(defn- prop-block [alias constructors]
  {:block/schema-version 1 :block/alias alias :block/universes []
   :block/parameters [{:parameter/name 'P :parameter/type [:sort [:zero]]}
                      {:parameter/name 'Q :parameter/type [:sort [:zero]]}]
   :block/sort-level [:zero] :block/constructors constructors})

(deftest prop-blocks-eliminate-like-lean
  (let [two (kernel/add-inductive-block
             (direct-term-corpus/build-environment)
             (prop-block 'export/Or [{:constructor/alias 'export/inl :constructor/fields [{:field/name 'h :field/type [:var 'P]}]}
                                     {:constructor/alias 'export/inr :constructor/fields [{:field/name 'h :field/type [:var 'Q]}]}]))
        one (kernel/add-inductive-block
             (:environment two)
             (prop-block 'export/And [{:constructor/alias 'export/both
                                       :constructor/fields [{:field/name 'p :field/type [:var 'P]}
                                                            {:field/name 'q :field/type [:var 'Q]}]}]))
        environment (:environment one)
        or-result (lean-export/export-closure environment 'export/Or.rec {})
        and-result (lean-export/export-closure environment 'export/And.rec {})]
    (is (= :accepted (:status two) (:status one)))
    (is (:prop-only-elimination? (last (:units or-result))) "two constructors: Prop motives only, as in Lean")
    (is (not (:prop-only-elimination? (last (:units and-result)))) "one constructor of proofs: large elimination")
    (is (re-find #":=\n  @RainbowXcheck\.export_Or_\w+\.rec\n" (:source or-result)) "no motive universe")
    (is (string/includes? (:source and-result) "rainbowCheckRec.{_rainbow_motive_universe}"))
    (when (.isFile (io/file lean-binary))
      (doseq [result [or-result and-result]]
        (let [run (run-lean (:source result))]
          (is (zero? (:exit run)) (:log run)))))))

(deftest profile-principles-are-lean-theorems-proved-from-lean-axioms
  (let [environment (-> (proposition/build-environment) (profile/activate :mathlib-complete-logic)
                        :environment (profile/activate :choice-bearing) :environment)
        expected {'logic/excluded-middle "[propext, Classical.choice, Quot.sound]"
                  'logic/proof-irrelevance nil
                  'logic/function-extensionality "[Quot.sound]"
                  'logic/proposition-extensionality "[propext]"
                  'logic/choice "[Classical.choice]"}]
    (doseq [[alias axioms] expected]
      (let [result (lean-export/export-closure environment alias {})]
        (is (= :exported (:status result)) (pr-str alias))
        (is (= (if (= 'logic/choice alias) "noncomputable def" "theorem") (:lean/keyword result)))
        (is (not (string/includes? (:source result) "\naxiom ")))
        (when (.isFile (io/file lean-binary))
          (let [run (run-lean (:source result))
                line (axioms-line (:log run) (:lean/name result))]
            (is (zero? (:exit run)) (:log run))
            (is (if axioms (string/ends-with? line (str "depends on axioms: " axioms))
                    (string/ends-with? line "does not depend on any axioms"))
                (pr-str alias line))))))))

(deftest lean-rejects-a-closure-whose-statement-is-negated
  (when (.isFile (io/file lean-binary))
    (let [result (lean-export/export-closure @checkpoint 'nat/multiply-successor-right {})
          source (:source result)
          local (last (string/split (:lean/name result) #"\."))
          at (string/last-index-of source (str "\ntheorem " local))
          a (+ (string/index-of source " :\n  " at) 5)
          b (string/index-of source " :=\n  " a)
          run (run-lean (str (subs source 0 a) "(" (subs source a b) " → False)" (subs source b)))]
      (is (not (zero? (:exit run))))
      (is (string/includes? (:log run) "sorryAx")))))
