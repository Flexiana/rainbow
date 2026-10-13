(ns rainbow.milestones.ahof-decision-guarantee
  "Content-addressed evidence for the first credited AHoF decision audit."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as day54]
            [rainbow.checkpoint.frontier :as frontier]
            [rainbow.milestones.rational-value-iteration :as rational]
            [rainbow.curriculum.applied-higher-order-functions :as ahof]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.algorithms.proofs.decision-guarantee-audit :as audit]))

(def evidence-path
  "artifacts/ahof/decision-guarantee-audit-v0/evidence.edn")
(def checkpoint-path
  "artifacts/ahof/decision-guarantee-audit-v0/checkpoint.edn.gz")
(def default-input-checkpoint-path rational/checkpoint-path)

(defn- checked? [checked-environment id]
  (let [declaration (environment/declaration checked-environment id)]
    (= :checked
       (:status
        (kernel/check checked-environment
                      (:rainbow/value declaration)
                      (:rainbow/type declaration)
                      (set (:rainbow/universes declaration)))))))

(defn- core [checked-environment expression]
  (let [result (elaborate/core-expression checked-environment expression)]
    (when-not (= :elaborated (:status result))
      (throw (ex-info "AHoF audit expression rejected"
                      {:expression expression :result result})))
    (:term result)))

(defn- evaluation [checked-environment result-name expected-name]
  (let [normalized
        (kernel/normalize checked-environment
                          (core checked-environment
                                [:const result-name []]))
        expected (core checked-environment [:const expected-name []])]
    {:status (:status normalized)
     :result/name result-name
     :expected/name expected-name
     :matches? (= expected (:term normalized))}))

(defn build [input-checkpoint-path]
  (let [prior (day54/load-checkpoint input-checkpoint-path)]
    (when-not (= :replayed (:status prior))
      (throw (ex-info "AHoF audit input checkpoint rejected" {:prior prior})))
    (let [checked-environment
          (audit/extend-environment (:environment prior))
          definition-ids (audit/definition-ids checked-environment)
          theorem-ids (audit/theorem-ids checked-environment)
          evaluations
          [(evaluation checked-environment 'audit-ex-1/result 'audit/approved)
           (evaluation checked-environment 'audit-ex-2/result
                       'audit/missing-cap)
           (evaluation checked-environment 'audit-ex-3/result
                       'audit/cap-exceeds-bound)
           (evaluation checked-environment 'audit-ex-4/result
                       'audit/missing-support)]]
      {:prior prior :environment checked-environment
       :definition-ids definition-ids :theorem-ids theorem-ids
       :evaluations evaluations})))

(defn checkpoint [build]
  (let [value
        (frontier/checkpoint
         {:prior (:prior build)
          :environment (:environment build)
          :new-mappings [] :evaluations []})
        source-entry
        {:kind :ahof-decision-guarantee-audit-v0
         :algorithm/id "decision-guarantee-audit-v0"
         :proof-values :redacted}
        base
        (-> value
            (dissoc :rainbow.checkpoint/id)
            (update-in [:source :additional-statement-batches]
                       (fnil conj []) source-entry))]
    (assoc base :rainbow.checkpoint/id (canonical/content-id base))))

(defn evidence [build checkpoint-value replay]
  (let [environment (:environment build)
        theorem-ids (:theorem-ids build)
        definition-ids (:definition-ids build)
        axiom-profiles
        (into (sorted-map)
              (map (fn [[name id]] [name (kernel/axioms environment id)]))
              theorem-ids)
        all-ids (concat (vals definition-ids) (vals theorem-ids))
        proof-id (fn [name] (get theorem-ids name))
        claim-id (fn [name] (get definition-ids name))
        instances
        [{:instance/id :audit-ex-1
          :claim
          {:native/id (claim-id 'audit-ex-1/claim)
           :actions [:accept :renegotiate :decline]
           :outcomes {:accept :accept :renegotiate :renegotiate
                      :decline :decline}
           :loss {:accept "10/1" :renegotiate "4/1" :decline "0/1"}
           :bound "10/1"
           :declared-support [:accept :renegotiate :decline]}
          :premises
          {:cap {:present? true :value "10/1"}
           :support {:present? true}
           :info-field {:present? false}
           :no-hindsight {:present? true}}
          :result {:status :proved
                   :proof-id (proof-id 'audit-ex-1/all-losses-at-most-ten)
                   :audit-proof-id (proof-id 'audit-ex-1/audit-approved)}}
         {:instance/id :audit-ex-2
          :claim {:native/id (claim-id 'audit-ex-2/claim)
                  :same-actions-losses-and-bound-as :audit-ex-1}
          :premises
          {:cap {:present? false}
           :support {:present? true}
           :info-field {:present? false}
           :no-hindsight {:present? true}}
          :result {:status :refused :reason :missing-cap
                   :proof-id (proof-id 'audit-ex-2/refused-missing-cap)}}
         {:instance/id :audit-ex-3
          :claim {:native/id (claim-id 'audit-ex-3/claim)
                  :actions [:accept :renegotiate :decline]
                  :loss {:accept "10/1" :renegotiate "4/1" :decline "0/1"}
                  :cap "10/1" :bound "3/1"}
          :premises
          {:cap {:present? true :value "10/1"}
           :support {:present? true}
           :info-field {:present? false}
           :no-hindsight {:present? true}}
          :result {:status :refused :reason :cap-exceeds-bound
                   :proof-id
                   (proof-id 'audit-ex-3/refused-cap-exceeds-bound)}}
         {:instance/id :audit-ex-4
          :claim {:native/id (claim-id 'audit-ex-4/claim)
                  :same-actions-losses-and-bound-as :audit-ex-1}
          :premises
          {:cap {:present? true :value "10/1"}
           :support {:present? false}
           :info-field {:present? false}
           :no-hindsight {:present? true}}
          :result {:status :refused :reason :missing-support
                   :proof-id
                   (proof-id 'audit-ex-4/refused-missing-support)}}]
        passed?
        (and (= :replayed (:status replay))
             (every? #(checked? environment %) all-ids)
             (every? empty? (vals axiom-profiles))
             (every? :matches? (:evaluations build))
             (every? #(string? (get-in % [:result :proof-id])) instances))
        base
        {:status (if passed? :passed :failed)
         :packet/schema-version 1
         :algorithm/id "decision-guarantee-audit-v0"
         :source
         {:proof-origin :independent-native-rainbow
          :lean-imported? false :mathlib-proof-bodies-used? false
          :input-checkpoint/id (get-in build [:prior :checkpoint/id])}
         :native-model
         {:claim/type-id (claim-id 'audit/Claim)
          :claim/constructor-id (claim-id 'audit/claim)
          :action-representation :nat-tags
          :outcome-representation :nat-tags
          :actions/finite-set :finset-data/range
          :loss-domain :nonnegative-rational
          :premise-set
          {:representation :four-key-boolean-product
           :keys [:cap :support :info-field :no-hindsight]}
          :order
          {:representation :chain-of-exact-cross-multiplication-inequalities
           :base-id (claim-id 'nnrat/base-at-most)
           :preorder-id (claim-id 'nnrat/at-most)}}
         :required-theorems
         {:soundness
          {:native/name 'audit/decision-guarantee-sound
           :proof-id (proof-id 'audit/decision-guarantee-sound)
           :axioms #{}}
          :refusal-path
          {:native/name 'audit/refusal-path
           :proof-id (proof-id 'audit/refusal-path)
           :axioms #{}
           :semantics
           :refusal-certifies-missing-proof-route-not-falsity-of-bound}}
         :instances instances
         :evaluations (:evaluations build)
         :axiom-profiles axiom-profiles
         :trusted-base-delta :none
         :checkpoint
         {:id (:rainbow.checkpoint/id checkpoint-value)
          :kernel-replay (:status replay)
          :exact-mathlib-mappings (count (:mappings checkpoint-value))}
         :ahof-ledger-entry-draft
         {:ahof/id "decision-guarantee-audit-v0"
          :ahof/domain :decision-making
          :ahof/name "Finite Decision Guarantee Audit v0"
          :ahof/outcome :proved
          :ahof/specification
          {:soundness 'audit/decision-guarantee-sound
           :refusal 'audit/refusal-path}
          :ahof/shared-finset-foundations-counted-as-algorithm? false
          :ahof/catalog-entry? false}
         :not-claimed
         [:probability :causal-roi :customer-savings :real-analysis
          :clojure-production-program-correspondence
          :polymorphic-bundled-claim-record]}
        packet (assoc base :evidence/id (canonical/content-id base))]
    packet))

(defn ledger-entry [packet]
  (-> (:ahof-ledger-entry-draft packet)
      (assoc :ahof/evidence
             [{:kind :content-addressed-rainbow-evidence
               :evidence/id (:evidence/id packet)
               :checkpoint/id (get-in packet [:checkpoint :id])
               :soundness-proof-id
               (get-in packet [:required-theorems :soundness :proof-id])
               :refusal-proof-id
               (get-in packet [:required-theorems :refusal-path :proof-id])}])))

(defn run [input-checkpoint-path]
  (let [build (build input-checkpoint-path)
        checkpoint-value (checkpoint build)
        replay (day54/replay-checkpoint checkpoint-value)
        packet (evidence build checkpoint-value replay)]
    {:build build :checkpoint checkpoint-value :replay replay :evidence packet}))

(defn load-evidence [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :evidence/id))]
      (if (= expected (:evidence/id value))
        {:status :replayed :evidence/id expected :evidence value}
        {:status :rejected
         :error/category :ahof-audit/evidence-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :ahof-audit/evidence-read-failed
       :message (.getMessage throwable)})))

(defn- write-edn! [path value]
  (let [file (io/file path)]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command]]
  (try
    (if (= "replay" command)
      (let [result (load-evidence evidence-path)]
        (println (pr-str (dissoc result :evidence)))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [{:keys [checkpoint evidence]}
            (run (or command default-input-checkpoint-path))
            ledger-result (ahof/load-ledger ahof/ledger-path)]
        (when-not (= :replayed (:status ledger-result))
          (throw (ex-info "AHoF ledger rejected before credit"
                          {:ledger-result ledger-result})))
        (write-edn! evidence-path evidence)
        (frontier/write-checkpoint! checkpoint-path checkpoint)
        (ahof/write-credited-ledger!
         ahof/ledger-path
         (ahof/credit-result (:ledger ledger-result)
                             (ledger-entry evidence)))
        (println (pr-str evidence))
        (when-not (= :passed (:status evidence)) (System/exit 1))))
    (finally (shutdown-agents))))
