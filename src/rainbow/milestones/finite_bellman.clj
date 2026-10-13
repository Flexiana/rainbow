(ns rainbow.milestones.finite-bellman
  "Evidence report for the precommitted finite fixed-policy Bellman chain."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [rainbow.canonical :as canonical]
            [rainbow.checkpoint :as checkpoint]
            [rainbow.search.preset-late :as preset-late]
            [rainbow.elaborate :as elaborate]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.finite.bellman :as finite-bellman]
            [rainbow.math.finite.expectation :as finite-expectation]
            [rainbow.math.sets.finset.data :as finset-data]
            [rainbow.math.sets.finset.range :as finset-range]
            [rainbow.math.nat.order :as nat-order]))

(def precommit-path "artifacts/or-bellman-chain/precommit.edn")
(def report-path "artifacts/or-bellman-chain/report.edn")

(def target-support
  {'probability/two-state-uniform-normalized
   'probability/two-state-uniform-normalized
   'probability/two-state-identity-expectation
   'probability/two-state-identity-expectation
   'markov/two-state-rows-normalized
   'markov/two-state-rows-normalized
   'bellman/two-state-state-one-result
   'bellman/two-state-state-one-result
   'bellman/zero-data 'bellman/zero-data
   'bellman/fixed-policy-monotone 'bellman/fixed-policy-monotone})

(defn- load-precommit []
  (let [value (edn/read-string (slurp precommit-path))
        expected (canonical/content-id (dissoc value :precommit/id))]
    (when-not (= expected (:precommit/id value))
      (throw (ex-info "Bellman precommit identity mismatch"
                      {:expected expected :actual (:precommit/id value)})))
    value))

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
      (throw (ex-info "Bellman example expression rejected" {:result result})))
    (:term result)))

(defn- example-evaluation [checked-environment]
  (let [nat [:const 'data/Nat []]
        zero [:const 'data/zero []]
        successor [:const 'data/succ []]
        one [:app successor zero]
        two [:app successor one]
        three [:app successor two]
        four [:app successor three]
        five [:app successor four]
        expression
        [:app [:const 'bellman/fixed-policy-numerator [[:zero]]]
         nat two
         [:const 'or-example/two-state-space []]
         [:const 'or-example/uniform-transition []]
         [:const 'or-example/identity-value []]
         one [:const 'or-example/identity-value []] one]
        normalized
        (kernel/normalize checked-environment
                          (core checked-environment expression))]
    {:status (:status normalized)
     :expected-natural 5
     :matches-theorem-result?
     (= (core checked-environment five) (:term normalized))}))

(defn build-report []
  (let [precommit (load-precommit)
        checkpoint (checkpoint/load-checkpoint preset-late/checkpoint-path)
        _ (when-not (= :replayed (:status checkpoint))
            (throw (ex-info "Bellman baseline checkpoint rejected"
                            {:checkpoint checkpoint})))
        started (System/nanoTime)
        checked-environment
        (-> (:environment checkpoint)
            finset-range/extend-environment
            finset-data/extend-environment
            finite-expectation/extend-environment
            nat-order/extend-environment
            finite-bellman/extend-environment)
        rainbow-compute-ms
        (long (/ (- (System/nanoTime) started) 1000000))
        bellman-ids (finite-bellman/theorem-ids checked-environment)
        order-ids (nat-order/theorem-ids checked-environment)
        target-partitions
        (into {} (map (juxt :target/name :study/partition))
              (:precommit/targets precommit))
        evaluations
        (mapv
         (fn [[target support]]
           (let [id (get bellman-ids support)]
             {:target/name target
              :study/partition (get target-partitions target)
              :status (if (and id (checked? checked-environment id))
                        :proved :failed)
              :native/id id
              :axioms (when id (kernel/axioms checked-environment id))}))
         target-support)
        evaluator (example-evaluation checked-environment)
        proved (filterv #(= :proved (:status %)) evaluations)
        held-out (filterv #(= :held-out (:study/partition %)) evaluations)
        transfer (filterv #(= :transfer (:study/partition %)) evaluations)
        passed?
        (and (= (set (keys target-support))
                (set (map :target/name (:precommit/targets precommit))))
             (= 6 (count proved))
             (= 2 (count held-out))
             (= 1 (count transfer))
             (every? empty? (map :axioms evaluations))
             (every? #(checked? checked-environment %) (vals order-ids))
             (= :normalized (:status evaluator))
             (:matches-theorem-result? evaluator))
        base
        {:status (if passed? :passed :failed)
         :precommit/id (:precommit/id precommit)
         :capability
         {:kind :finite-fixed-policy-bellman
          :arithmetic :natural-numerators-with-explicit-scale
          :target-theorems bellman-ids
          :general-order-lemmas order-ids
          :axiom-profile #{}
          :trusted-base-delta :none}
         :experiment
         {:baseline-proved 0
          :candidate-proved (count proved)
          :targets (count evaluations)
          :held-out {:proved (count (filter #(= :proved (:status %)) held-out))
                     :targets (count held-out)}
          :transfer {:proved (count (filter #(= :proved (:status %)) transfer))
                     :targets (count transfer)}
          :evaluations evaluations
          :rainbow-compute-ms rainbow-compute-ms
          :ai-latency-ms :not-instrumented
          :search-states :not-applicable-direct-proof-construction
          :lemma-leverage
          {:new-general-order-lemmas (count order-ids)
           :newly-solved-held-out-targets (count held-out)
           :held-out-targets-per-order-lemma
           (/ (count held-out) (count order-ids))}}
         :executable-example
         {:state-count 2 :probability-scale 2 :discount-numerator 1
          :bellman-output-scale 8 :state-one-output-numerator 5
          :rainbow-evaluation evaluator}
         :coverage
         {:new-native-theorems (+ (count bellman-ids) (count order-ids))
          :new-mathlib-exact-mappings 0}
         :claim-boundaries
         {:mathematical-theorems-proved? true
          :rainbow-evaluator-computed-example? true
          :clojure-implementation-correspondence-proved? false
          :computed-output-satisfies-rainbow-theorem? true
          :raw-scaled-values-claimed-as-rational-quotient-field? false
          :contraction-or-fixed-point-proved? false
          :trusted-kernel-change :none}}
        report (assoc base :report/id (canonical/content-id base))]
    report))

(defn load-report [path]
  (try
    (let [value (edn/read-string (slurp path))
          expected (canonical/content-id (dissoc value :report/id))]
      (if (= expected (:report/id value))
        {:status :replayed :report/id expected}
        {:status :rejected :error/category :bellman/report-id-mismatch}))
    (catch Throwable throwable
      {:status :rejected :error/category :bellman/report-read-failed
       :message (.getMessage throwable)})))

(defn- write-report! [path value]
  (let [file (io/file (str path))]
    (.mkdirs (.getParentFile file))
    (spit file (str (pr-str value) "\n"))))

(defn -main [& [command]]
  (try
    (if (= "replay" command)
      (let [result (load-report report-path)]
        (println (pr-str result))
        (when-not (= :replayed (:status result)) (System/exit 1)))
      (let [report (build-report)]
        (write-report! report-path report)
        (println (pr-str report))
        (when-not (= :passed (:status report)) (System/exit 1))))
    (finally (shutdown-agents))))
