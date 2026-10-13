(ns rainbow.history.bool-nat-refinement
  "Checked Bool-to-Nat representation refinement and theorem transport."
  (:require [clojure.edn :as edn]
            [rainbow.canonical :as canonical]
            [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]
            [rainbow.transport :as transport]))

(def report-path "artifacts/day23/report.edn")

(defn- constant [checked-environment alias levels]
  (term/constant (environment/resolve-id checked-environment alias) levels))

(defn- apply* [function & arguments]
  (reduce term/application function arguments))

(defn- add! [checked-environment alias kind type value]
  (let [result
        (kernel/add-declaration
         checked-environment
         {:rainbow/kind kind
          :rainbow/aliases #{alias}
          :rainbow/universes []
          :rainbow/type type
          :rainbow/value value
          :rainbow/transparency (if (= :definition kind) :reducible :opaque)
          :rainbow/dependencies (into (term/constants type) (term/constants value))
          :rainbow/provenance {:origin :native :producer :day23-transport}
          :rainbow/schema-version 1})]
    (when-not (= :accepted (:status result))
      (throw (ex-info "Transport declaration rejected"
                      {:alias alias :result result})))
    (:environment result)))

(defn build []
  (let [base (inductive/build-environment)
        bool (constant base 'data/Bool [])
        nat (constant base 'data/Nat [])
        false-term (constant base 'data/false [])
        true-term (constant base 'data/true [])
        zero-term (constant base 'data/zero [])
        successor (constant base 'data/succ [])
        one (apply* successor zero-term)
        bool-rec-type (constant base 'data/Bool.rec [inductive/type-level])
        nat-rec-type (constant base 'data/Nat.rec [inductive/type-level])
        encode-type (term/pi-term bool nat)
        encode-value
        (term/lambda-term
         bool
         (apply* bool-rec-type (term/lambda-term bool nat)
                 zero-term one (term/bound 0)))
        with-encode (add! base 'transport/bool->nat :definition
                          encode-type encode-value)
        encode (constant with-encode 'transport/bool->nat [])
        decode-type (term/pi-term nat bool)
        decode-value
        (term/lambda-term
         nat
         (apply* nat-rec-type (term/lambda-term nat bool)
                 false-term
                 (term/lambda-term nat (term/lambda-term bool true-term))
                 (term/bound 0)))
        with-decode (add! with-encode 'transport/nat->bool :definition
                          decode-type decode-value)
        decode (constant with-decode 'transport/nat->bool [])
        eq-bool (constant with-decode 'equality/Eq [inductive/type-level])
        reflexive (constant with-decode 'equality/reflexive [inductive/type-level])
        roundtrip-body
        (apply* eq-bool bool
                (apply* decode (apply* encode (term/bound 0)))
                (term/bound 0))
        roundtrip-type (term/pi-term bool roundtrip-body)
        roundtrip-value
        (term/lambda-term
         bool
         (apply* (constant with-decode 'data/Bool.rec [term/zero-level])
                 (term/lambda-term bool roundtrip-body)
                 (apply* reflexive bool false-term)
                 (apply* reflexive bool true-term)
                 (term/bound 0)))
        with-roundtrip (add! with-decode 'transport/bool-source-retraction
                             :theorem roundtrip-type roundtrip-value)
        eq-nat (constant with-roundtrip 'equality/Eq [inductive/type-level])
        false-preserved-type (apply* eq-nat nat (apply* encode false-term) zero-term)
        true-preserved-type (apply* eq-nat nat (apply* encode true-term) one)
        with-false (add! with-roundtrip 'transport/false-preserved :theorem
                         false-preserved-type (apply* reflexive nat zero-term))
        with-true (add! with-false 'transport/true-preserved :theorem
                        true-preserved-type (apply* reflexive nat one))
        mapping
        {:transport/schema-version 1
         :transport/relation :representation-refinement
         :transport/source {:concept :boolean :representation :inductive-bool
                            :type bool}
         :transport/target {:concept :boolean :representation :zero-one-nat
                            :type nat
                            :image {:zero false :one true :other :outside-image}}
         :transport/forward (environment/resolve-id with-true 'transport/bool->nat)
         :transport/backward (environment/resolve-id with-true 'transport/nat->bool)
         :transport/laws
         {:source-retraction
          (environment/resolve-id with-true 'transport/bool-source-retraction)}
         :transport/transported-theorems
         [{:source/claim {:constructor :false}
           :target/theorem-id (environment/resolve-id with-true
                                                      'transport/false-preserved)}
          {:source/claim {:constructor :true}
           :target/theorem-id (environment/resolve-id with-true
                                                      'transport/true-preserved)}]}
        checked (transport/validate with-true mapping)]
    {:environment with-true :mapping mapping :checked checked}))

(defn report []
  (let [{:keys [environment checked]} (build)
        aliases '[transport/bool->nat transport/nat->bool
                  transport/bool-source-retraction
                  transport/false-preserved transport/true-preserved]
        normalized
        (into {}
              (map (fn [source]
                     [source
                      (:term
                       (kernel/normalize
                        environment
                        (apply* (constant environment 'transport/nat->bool [])
                                (apply* (constant environment 'transport/bool->nat [])
                                        (constant environment source [])))))]))
              '[data/false data/true])
        expected {'data/false (constant environment 'data/false [])
                  'data/true (constant environment 'data/true [])}
        passed? (and (= :checked (:status checked))
                     (= expected normalized)
                     (empty? (:axioms checked)))
        base {:status (if passed? :passed :failed)
              :transport/id (:transport/id checked)
              :relation :representation-refinement
              :representations {:source :inductive-bool :target :zero-one-nat}
              :adapters {:forward :kernel-checked :backward :kernel-checked}
              :laws {:source-retraction :kernel-checked
                     :transported-constructor-theorems 2}
              :kernel-rechecks (:kernel-rechecks checked)
              :axioms (:axioms checked)
              :normalization-cases 2
              :declarations (count aliases)
              :boundary {:target-outside-image :not-equivalent
                         :transport-validator :untrusted
                         :kernel-rule-added? false}
              :trusted-base-change :none}]
    (assoc base :report/id (canonical/content-id base))))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :transport/report-id-mismatch
         :expected expected :actual (:report/id value)}))
    (catch Throwable throwable
      {:status :rejected :error/category :transport/report-read-failed
       :message (.getMessage throwable)})))

(defn -main [& [command path]]
  (case command
    "hash" (println (:report/id (report)))
    "replay" (let [result (load-report (or path report-path))]
               (println (pr-str result))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
