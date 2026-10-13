(ns rainbow.history.first-tactic-program
  "First theorem constructed as an immutable tactic program."
  (:require [clojure.java.io :as io]
            [rainbow.history.direct-term-corpus :as direct-term-corpus]
            [rainbow.elaborate :as elaborate]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.search :as search]
            [rainbow.session :as session]
            [rainbow.storage :as storage]
            [rainbow.tactic :as tactic]))

(def target
  (:type (first (filter #(= 'logic/implication-transitivity (:name %)) direct-term-corpus/proofs))))

(def tactic-program
  [{:tactic :intro :name 'A}
   {:tactic :intro :name 'B}
   {:tactic :intro :name 'C}
   {:tactic :intro :name 'f}
   {:tactic :intro :name 'g}
   {:tactic :intro :name 'x}
   {:tactic :apply :term [:bound 1]}
   {:tactic :apply :term [:bound 2]}
   {:tactic :assumption}])

(defn interpret [step]
  (case (:tactic step)
    :intro (tactic/intro (:name step))
    :apply (tactic/apply (:term step))
    :assumption (tactic/assumption)
    :exact (tactic/exact (:term step))))

(defn prove []
  (let [started (proof/start (direct-term-corpus/build-environment) target)]
    (reduce (fn [result step]
              (if (contains? #{:ready :progress} (:status result))
                (tactic/run (:state result) (interpret step))
                (reduced result)))
            started
            tactic-program)))

(defn forall [names body]
  [:forall (mapv (fn [name] [name 'Prop]) names) body])

(def development-surfaces
  [{:name 'development/identity
    :surface (forall '[A] [:-> 'A 'A])}
   {:name 'development/constant-left
    :surface (forall '[A B] [:-> 'A 'B 'A])}
   {:name 'development/constant-right
    :surface (forall '[A B] [:-> 'A 'B 'B])}
   {:name 'development/apply
    :surface (forall '[A B] [:-> [:-> 'A 'B] 'A 'B])}
   {:name 'development/apply-flipped
    :surface (forall '[A B] [:-> 'A [:-> 'A 'B] 'B])}
   {:name 'development/compose-backward
    :surface (forall '[A B C] [:-> [:-> 'B 'C] [:-> 'A 'B] 'A 'C])}
   {:name 'development/compose-forward
    :surface (forall '[A B C] [:-> [:-> 'A 'B] [:-> 'B 'C] 'A 'C])}
   {:name 'development/select-first-of-three
    :surface (forall '[A B C] [:-> 'A 'B 'C 'A])}
   {:name 'development/select-second-of-three
    :surface (forall '[A B C] [:-> 'A 'B 'C 'B])}
   {:name 'development/select-third-of-three
    :surface (forall '[A B C] [:-> 'A 'B 'C 'C])}
   {:name 'development/flip-arguments
    :surface (forall '[A B C] [:-> [:-> 'A 'B 'C] 'B 'A 'C])}
   {:name 'development/duplicate-argument
    :surface (forall '[A B] [:-> [:-> 'A 'A 'B] 'A 'B])}])

(def held-out-surfaces
  [{:name 'held-out/compose-three-backward
    :surface (forall '[A B C D]
                     [:-> [:-> 'C 'D] [:-> 'B 'C] [:-> 'A 'B] 'A 'D])}
   {:name 'held-out/compose-three-forward
    :surface (forall '[A B C D]
                     [:-> [:-> 'A 'B] [:-> 'B 'C] [:-> 'C 'D] 'A 'D])}
   {:name 'held-out/substitution-combinator
    :surface (forall '[A B C]
                     [:-> [:-> 'A 'B 'C] [:-> 'A 'B] 'A 'C])}
   {:name 'held-out/shared-input
    :surface (forall '[A B C]
                     [:-> [:-> 'A 'B] [:-> 'A 'B 'C] 'A 'C])}
   {:name 'held-out/higher-order-application
    :surface (forall '[A B C]
                     [:-> [:-> [:-> 'A 'B] 'C] [:-> 'A 'B] 'C])}
   {:name 'held-out/continuation-chain
    :surface (forall '[A B C D]
                     [:-> [:-> 'A 'B] [:-> 'B 'C] [:-> 'C 'D] 'A 'D])}
   {:name 'held-out/repeated-input
    :surface (forall '[A B] [:-> [:-> 'A 'A 'B] 'A 'A 'B])}
   {:name 'held-out/select-second-of-four
    :surface (forall '[A B C D] [:-> 'A 'B 'C 'D 'B])}
   {:name 'held-out/ignore-alternative
    :surface (forall '[A B C]
                     [:-> [:-> 'A 'B] [:-> 'A 'C] 'A 'B])}
   {:name 'held-out/chain-with-extra-input
    :surface (forall '[A B C]
                     [:-> 'A [:-> 'A 'B] [:-> 'B 'C] 'C])}])

(defn targets [entries]
  (mapv (fn [entry]
          (let [result (elaborate/type-expression (:surface entry))]
            (when-not (= :elaborated (:status result))
              (throw (ex-info "Corpus surface failed to elaborate"
                              {:entry entry :result result})))
            (assoc entry :type (:term result))))
        entries))

(def development-targets (targets development-surfaces))
(def held-out-targets (targets held-out-surfaces))

(defn prove-target [environment {:keys [name type] :as target} budget]
  (let [started (proof/start environment type)
        result (if (= :ready (:status started))
                 (search/prove (:state started) budget)
                 started)]
    (assoc result :job/id name :target target)))

(defn register-proof [environment result]
  (if-not (= :proved (:status result))
    {:status :rejected :cause result}
    (kernel/add-declaration
     environment
     {:rainbow/kind :theorem
      :rainbow/aliases #{(:job/id result)}
      :rainbow/universes []
      :rainbow/type (get-in result [:proof :proof/type])
      :rainbow/value (get-in result [:proof :proof/term])
      :rainbow/transparency :opaque
      :rainbow/dependencies #{}
      :rainbow/provenance {:origin :native :producer :bounded-search}
      :rainbow/schema-version 1})))

(defn run-targets [environment target-list budget]
  (reduce (fn [{:keys [environment results]} target]
            (let [result (prove-target environment target budget)
                  registration (register-proof environment result)]
              (if-not (= :accepted (:status registration))
                (reduced {:environment environment
                          :results (conj results (assoc result :registration registration))
                          :status :failed})
                {:environment (:environment registration)
                 :results (conj results (assoc result
                                          :declaration (:declaration registration)))
                 :status :passed})))
          {:environment environment :results [] :status :passed}
          target-list))

(defn run-corpus
  ([] (run-corpus {:states 2000 :depth 32 :wall-ms 10000}))
  ([budget]
   (let [development (run-targets (direct-term-corpus/build-environment) development-targets budget)
         held-out (if (= :passed (:status development))
                    (run-targets (:environment development) held-out-targets budget)
                    {:status :not-run :results [] :environment (:environment development)})]
     {:status (if (and (= :passed (:status development))
                       (= :passed (:status held-out)))
                :passed :failed)
      :environment (:environment held-out)
      :development (:results development)
      :held-out (:results held-out)})))

(defn partial-session []
  (let [started (proof/start (direct-term-corpus/build-environment) target)]
    (:state
     (reduce (fn [result name]
               (tactic/run (:state result) (tactic/intro name)))
             started
             '[A B C f g x]))))

(defn resume-session [state]
  (reduce (fn [result step]
            (if (contains? #{:ready :progress} (:status result))
              (tactic/run (:state result) (interpret step))
              (reduced result)))
          {:status :ready :state state}
          [{:tactic :apply :term [:bound 1]}
           {:tactic :apply :term [:bound 2]}
           {:tactic :assumption}]))

(defn report []
  (let [result (run-corpus)
        development (:development result)
        held-out (:held-out result)]
    {:status (:status result)
     :seed-proofs (+ (count development) (count held-out))
     :development {:proved (count (filter #(= :proved (:status %)) development))
                   :states (reduce + (map #(get-in % [:telemetry :states-created] 0)
                                         development))}
     :held-out {:proved (count (filter #(= :proved (:status %)) held-out))
                :states (reduce + (map #(get-in % [:telemetry :states-created] 0)
                                      held-out))}
     :declarations (count (get-in result [:environment :rainbow.environment/declarations]))}))

(defn record-baseline! [directory]
  (let [environment-path (str directory "/environment.edn")
        runs-path (str directory "/runs.edn")
        corpus (run-corpus)
        impossible (:term (elaborate/type-expression
                           (forall '[A B] [:-> 'A 'B])))
        blocked (search/prove (:state (proof/start (direct-term-corpus/build-environment) impossible)))]
    (io/make-parents environment-path)
    (if (or (.exists (io/file environment-path)) (.exists (io/file runs-path)))
      {:status :rejected
       :error {:error/category :corpus/artifact-exists
               :directory directory}}
      (do
        (persistence/save-environment! (:environment corpus) environment-path)
        (storage/append-run! runs-path :held-out/compose-three-backward
                             (first (:held-out corpus)))
        (storage/append-run! runs-path :held-out/uninhabited-implication blocked)
        {:status :recorded
         :environment environment-path
         :runs runs-path
         :corpus (report)
         :blocked {:status (:status blocked)
                   :remaining (count (:remaining blocked))
                   :attempts (count (:attempts blocked))}}))))

(defn -main [& [command path]]
  (case command
    "resume" (let [loaded (session/load! path)
                   result (if (= :valid (:status loaded))
                            (resume-session (:state loaded))
                            loaded)]
               (println (pr-str {:status (:status result)
                                 :kernel (get-in result [:kernel :status])}))
               (when-not (= :proved (:status result)) (System/exit 1)))
    "record" (let [result (record-baseline! path)]
               (println (pr-str result))
               (when-not (= :recorded (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
