(ns rainbow.main-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.foreign.mathlib :as mathlib]
            [rainbow.history.direct-term-corpus :as corpus]
            [rainbow.kernel :as kernel]
            [rainbow.main :as main]))

(def ^:private empty-env (environment/empty-environment))
(def ^:private checked-env (delay (corpus/build-environment)))
(defn- bundle []
  (main/proof-bundle {:checkpoint "test-base" :modules []
                      :base-env empty-env :env @checked-env
                      :claims (map :name corpus/proofs)}))

(defn- replay-base [path]
  (assert (= "test-base" path))
  {:status :replayed :environment empty-env})

;; A tiny proof-module fixture using the real kernel-checked direct-term corpus.
(defn extend-environment [env] env)
(defn theorem-ids [env]
  (let [alias (:name (first corpus/proofs))]
    {alias (environment/resolve-id env alias)}))

;; A reproducible milestone fixture with an actual kernel-replayable checkpoint.
(def default-input-checkpoint-path "reproduce-input")
(def checkpoint-path "reproduce-recorded")
(defn run [path]
  (assert (= default-input-checkpoint-path path))
  {:checkpoint (frontier/checkpoint
                {:environment @checked-env
                 :prior {:source {:version mathlib/pinned-version
                                  :commit mathlib/pinned-commit}
                         :remaining-targets []}})})

(deftest reproduction-compares-content-rather-than-only-stored-ids
  (let [original (:checkpoint (run default-input-checkpoint-path))
        recorded (checkpoint/replay-checkpoint original)]
    (is (= :replayed (:status recorded)))
    (with-redefs [checkpoint/load-checkpoint (fn [path]
                                              (assert (= checkpoint-path path))
                                              recorded)]
      (is (true? (:match? (main/reproduce-milestone 'rainbow.main-test))))
      (doseq [changed [(assoc original :remaining-targets [{:foreign/name 'changed/target}])
                       (assoc original :environment {})
                       (dissoc original :rainbow.checkpoint/id)]]
        (with-redefs [run (fn [_] {:checkpoint changed})]
          (is (not (:match? (main/reproduce-milestone 'rainbow.main-test)))))))))

(deftest namespace-verification-checks-the-advertised-alias
  (is (= :checked (-> (main/verify-namespace @checked-env 'rainbow.main-test)
                      :theorems first :status)))
  (with-redefs [theorem-ids (fn [env]
                            {'uninstalled/claim (environment/resolve-id env (:name (first corpus/proofs)))})]
    (is (not= :checked (-> (main/verify-namespace @checked-env 'rainbow.main-test)
                          :theorems first :status)))))

(deftest a-bundle-module-must-return-an-environment
  (let [resolve ns-resolve]
    (with-redefs [ns-resolve (fn [n v]
                              (when-not (and (= n 'rainbow.main-test)
                                             (#{'theorem-ids 'definition-ids} v))
                                (resolve n v)))]
      (is (:bundle? (main/verify-namespace empty-env 'rainbow.main-test)))
      (with-redefs [extend-environment (constantly nil)]
        (is (:error (main/verify-namespace empty-env 'rainbow.main-test)))))))

(deftest bundles-require-a-nonempty-claim-map
  (with-redefs [checkpoint/load-checkpoint replay-base]
    (is (true? (:ok? (main/check-bundle (bundle)))))
    (doseq [claims [nil {} []]]
      (testing (pr-str claims)
        (is (false? (:ok? (main/check-bundle (assoc (bundle) :claims claims)))))))))

(deftest bundles-preserve-new-aliases-for-existing-declarations
  (let [base @checked-env
        original (:name (first corpus/proofs))
        id (environment/resolve-id base original)
        declaration (environment/declaration base id)
        result (kernel/add-declaration base (update declaration :rainbow/aliases conj 'exported/identity))
        exported (main/proof-bundle {:checkpoint "alias-base" :modules []
                                    :base-env base :env (:environment result)
                                    :claims ['exported/identity]})]
    (is (= :accepted (:status result)))
    (is (= (environment/environment-id base)
           (environment/environment-id (:environment result)))
        "adding an alias does not change the semantic environment ID")
    (is (= 1 (count (:declarations exported))))
    (with-redefs [checkpoint/load-checkpoint
                  (fn [path]
                    (assert (= "alias-base" path))
                    {:status :replayed :environment base})]
      (let [replayed (main/check-bundle exported)]
        (is (true? (:ok? replayed)))
        (is (= id (get-in replayed [:claims 'exported/identity :resolved])))))))

(defn- add-bool-value [env alias]
  (let [bool-id (environment/resolve-id env 'data/Bool)
        true-id (environment/resolve-id env 'data/true)
        result (kernel/add-declaration
                env {:rainbow/kind :definition :rainbow/aliases #{alias}
                     :rainbow/universes [] :rainbow/transparency :reducible
                     :rainbow/type [:const bool-id []] :rainbow/value [:const true-id []]
                     :rainbow/dependencies #{bool-id true-id}})]
    (assert (= :accepted (:status result)) (pr-str result))
    (:environment result)))

(defn- block-bundle []
  (let [block (kernel/add-inductive-block @checked-env inductive/bool-spec)]
    (assert (= :accepted (:status block)) (pr-str block))
    (main/proof-bundle {:checkpoint "block-base" :modules [] :base-env @checked-env
                        :env (add-bool-value (:environment block) 'bundle/true-value)
                        :claims ['bundle/true-value]})))

(deftest bundles-replay-new-inductive-blocks-atomically
  (with-redefs [checkpoint/load-checkpoint (fn [_] {:status :replayed :environment @checked-env})]
    (let [exported (edn/read-string (pr-str (block-bundle)))
          replayed (main/check-bundle exported)]
      (is (= 2 (:rainbow.bundle/schema-version exported)))
      (is (= [:inductive-block :declaration] (mapv :entry/kind (:entries exported))))
      (is (true? (:ok? replayed)) (pr-str replayed))
      (is (= :checked (get-in replayed [:claims 'bundle/true-value :status])))
      (is (= #{} (get-in replayed [:claims 'bundle/true-value :axioms]))))))

(deftest block-bundles-reject-forgeries-and-invalid-entry-order
  (with-redefs [checkpoint/load-checkpoint (fn [_] {:status :replayed :environment @checked-env})]
    (let [b (block-bundle)
          forged (main/check-bundle (assoc-in b [:entries 0 :entry/value :rainbow/id] "sha256:forged"))
          reversed (main/check-bundle (update b :entries #(vec (reverse %))))
          unknown (main/check-bundle (assoc-in b [:entries 0 :entry/kind] :not-a-kind))]
      (is (false? (:ok? forged)))
      (is (re-find #":kernel/forged-inductive-block-id" (:error forged)))
      (is (false? (:ok? reversed)))
      (is (re-find #":kernel/unknown-constant" (:error reversed)))
      (is (false? (:ok? unknown)))
      (is (re-find #":bundle/unknown-entry-kind" (:error unknown)))
      (doseq [malformed [(dissoc b :entries) (assoc b :entries {})
                         (assoc b :declarations [])]]
        (is (false? (:ok? (main/check-bundle malformed))))))))

(deftest schema-one-bundles-remain-compatible-and-unambiguous
  (with-redefs [checkpoint/load-checkpoint replay-base]
    (let [b (bundle)]
      (is (= 1 (:rainbow.bundle/schema-version b)))
      (is (true? (:ok? (main/check-bundle (edn/read-string (pr-str b))))))
      (is (false? (:ok? (main/check-bundle (assoc b :entries [])))))
      (is (false? (:ok? (main/check-bundle (dissoc b :declarations))))))))

(deftest re-aliased-blocks-are-exported-only-once
  (let [base (:environment (kernel/add-inductive-block @checked-env inductive/bool-spec))
        renamed-spec (-> inductive/bool-spec
                         (assoc :block/alias 'exported/Bool)
                         (assoc-in [:block/constructors 0 :constructor/alias] 'exported/false)
                         (assoc-in [:block/constructors 1 :constructor/alias] 'exported/true))
        added (kernel/add-inductive-block base renamed-spec)
        _ (is (= :accepted (:status added)))
        b (main/proof-bundle {:checkpoint "block-alias-base" :modules [] :base-env base
                              :env (add-bool-value (:environment added) 'bundle/renamed-true)
                              :claims ['bundle/renamed-true]})]
    (is (= [:inductive-block :declaration] (mapv :entry/kind (:entries b))))
    (with-redefs [checkpoint/load-checkpoint (fn [_] {:status :replayed :environment base})]
      (is (true? (:ok? (main/check-bundle b)))))))

(deftest bundles-still-reject-invalid-evidence
  (with-redefs [checkpoint/load-checkpoint replay-base]
    (let [b (bundle)
          alias (first (keys (:claims b)))]
      (doseq [bad [(assoc b :rainbow.bundle/schema-version 999)
                   (assoc-in b [:claims alias :id] "sha256:wrong")
                   (assoc-in b [:claims alias :axioms] #{'unrecorded/axiom})
                   (assoc-in b [:declarations 0 :rainbow/value] [:bound 0])]]
        (is (false? (:ok? (main/check-bundle bad))))))))

(deftest bundle-writer-preserves-reserved-symbol-aliases
  (let [base @checked-env
        id (environment/resolve-id base (:name (first corpus/proofs)))
        aliases '#{exported/true exported/false exported/nil}
        added (kernel/add-declaration
               base (update (environment/declaration base id) :rainbow/aliases into aliases))
        b (main/proof-bundle {:checkpoint "writer-base" :modules [] :base-env base
                              :env (:environment added) :claims aliases})
        file (java.io.File/createTempFile "rainbow-bundle-" ".edn")]
    (is (= :accepted (:status added)))
    (try
      (binding [*print-namespace-maps* true]
        (main/write-bundle! file b))
      (let [read-back (edn/read-string (slurp file))]
        (is (= aliases (set (keys (:claims read-back)))))
        (with-redefs [checkpoint/load-checkpoint (fn [_] {:status :replayed :environment base})]
          (is (true? (:ok? (main/check-bundle read-back))))))
      (finally (.delete file)))))

(deftest bundle-writer-is-independent-of-diagnostic-print-settings
  (let [b (with-meta (assoc (bundle) :meta {:description "a proof with spaces"
                                          :nested [1 [2 [3]]]})
                    {:diagnostic true})
        file (java.io.File/createTempFile "rainbow-bundle-" ".edn")]
    (try
      (binding [*print-length* 1 *print-level* 1 *print-meta* true
                *print-readably* false]
        (main/write-bundle! file b))
      (is (= b (edn/read-string (slurp file))))
      (finally (.delete file)))))

(deftest malformed-budgets-return-a-failure-result
  (with-redefs [checkpoint/load-checkpoint replay-base]
    (is (false? (:ok? (main/check-bundle (assoc (bundle) :check {:reductions "bad"})))))
    (is (false? (:ok? (main/check-bundle (bundle) "bad"))))))

(deftest bundle-command-needs-at-least-one-path
  (doseq [args [[] ["--reductions" "1000"]]]
    (let [result (atom nil)]
      (with-out-str (reset! result (#'main/verify-bundles-main args)))
      (is (false? @result)))))

(deftest bundle-command-reports-every-file-after-read-errors
  (with-redefs [checkpoint/load-checkpoint replay-base
                slurp (fn [path]
                        (case path
                          "missing.edn" (throw (java.io.FileNotFoundException. path))
                          "malformed.edn" "{"
                          "valid.edn" (pr-str (bundle))))]
    (let [result (atom nil)
          output (with-out-str
                   (reset! result (#'main/verify-bundles-main
                                   ["missing.edn" "malformed.edn" "valid.edn"])))]
      (is (false? @result))
      (is (re-find #"FAIL\s+missing.edn" output))
      (is (re-find #"FAIL\s+malformed.edn" output))
      (is (re-find #"OK\s+valid.edn" output)))))
