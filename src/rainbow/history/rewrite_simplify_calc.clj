(ns rainbow.history.rewrite-simplify-calc
  "Rewrite, simplify, and calc proofs reconstructed from immutable proof states."
  (:require [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.math.logic.equality :as equality]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(defn theorem-type [environment alias]
  (:rainbow/type (environment/declaration environment
                                          (environment/resolve-id environment alias))))

(defn after-intros [environment target count]
  (tactic/run (:state (proof/start environment target {:universes ['u]}))
              (tactic/repeat (tactic/intro) {:max count})))

(defn prove-substitution [environment]
  (let [introduced (after-intros environment
                                 (theorem-type environment 'equality/substitution) 6)
        rewritten (tactic/run (:state introduced) (tactic/rewrite [:bound 2]))]
    (tactic/run (:state rewritten) (tactic/assumption))))

(defn prove-reverse-substitution [environment]
  (let [introduced (after-intros environment
                                 (theorem-type environment 'equality/reverse-substitution) 6)
        rewritten (tactic/run (:state introduced)
                              (tactic/rewrite [:bound 2] {:direction :backward}))]
    (tactic/run (:state rewritten) (tactic/assumption))))

(defn prove-transitive [environment]
  (let [introduced (after-intros environment
                                 (theorem-type environment 'equality/transitive) 6)]
    (tactic/run (:state introduced) (tactic/calc [[:bound 1] [:bound 0]]))))

(defn prove-reflexive [environment]
  (let [introduced (after-intros environment
                                 (theorem-type environment 'equality/reflexive) 2)]
    (tactic/run (:state introduced) (tactic/simplify []))))

(def proof-jobs
  [{:name 'rewrite/substitution :source 'equality/substitution :prove prove-substitution}
   {:name 'rewrite/reverse-substitution
    :source 'equality/reverse-substitution :prove prove-reverse-substitution}
   {:name 'rewrite/transitive-calc :source 'equality/transitive :prove prove-transitive}
   {:name 'rewrite/reflexive-simp :source 'equality/reflexive :prove prove-reflexive}])

(defn register [environment {:keys [name source prove]}]
  (let [result (prove environment)]
    (when-not (= :proved (:status result))
      (throw (ex-info "Day-6 tactic proof failed" {:name name :result result})))
    (let [type (theorem-type environment source)
          value (get-in result [:proof :proof/term])
          declaration-result
          (kernel/add-declaration
           environment
           {:rainbow/kind :theorem
            :rainbow/aliases #{name}
            :rainbow/universes (if (contains? #{'equality/substitution
                                                'equality/reverse-substitution
                                                'equality/transitive
                                                'equality/reflexive} source)
                                 ['u] [])
            :rainbow/type type
            :rainbow/value value
            :rainbow/transparency :opaque
            :rainbow/dependencies (into (term/constants type) (term/constants value))
            :rainbow/provenance {:origin :native :producer :day-6-tactics}
            :rainbow/schema-version 1})]
      (when-not (= :accepted (:status declaration-result))
        (throw (ex-info "Day-6 tactic declaration rejected"
                        {:name name :result declaration-result})))
      {:environment (:environment declaration-result)
       :result result
       :declaration (:declaration declaration-result)})))

(defn build []
  (reduce (fn [{:keys [environment results]} job]
            (let [registered (register environment job)]
              {:environment (:environment registered)
               :results (conj results (dissoc registered :environment))}))
          {:environment (equality/build-environment) :results []}
          proof-jobs))

(defn report []
  (let [{:keys [environment results]} (build)]
    {:status :passed
     :proofs (count results)
     :declarations (count (:rainbow.environment/declarations environment))
     :axioms (into {} (map (fn [{:keys [name]}]
                             [name (kernel/axioms environment name)])
                           proof-jobs))
     :events (frequencies (mapcat #(map :event/tactic
                                        (get-in % [:result :proof :proof/history]))
                                  results))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (:environment (build)) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
