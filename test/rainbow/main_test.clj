(ns rainbow.main-test
  (:require [clojure.test :refer [deftest is testing]]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.environment :as environment]
            [rainbow.history.direct-term-corpus :as corpus]
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

(deftest bundles-still-reject-invalid-evidence
  (with-redefs [checkpoint/load-checkpoint replay-base]
    (let [b (bundle)
          alias (first (keys (:claims b)))]
      (doseq [bad [(assoc b :rainbow.bundle/schema-version 2)
                   (assoc-in b [:claims alias :id] "sha256:wrong")
                   (assoc-in b [:claims alias :axioms] #{'unrecorded/axiom})
                   (assoc-in b [:declarations 0 :rainbow/value] [:bound 0])]]
        (is (false? (:ok? (main/check-bundle bad))))))))

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
