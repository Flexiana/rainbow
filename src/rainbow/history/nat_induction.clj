(ns rainbow.history.nat-induction
  "Eight Nat theorems, including two proofs built through visible induction states."
  (:require [rainbow.data.inductive :as inductive]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.persistence :as persistence]
            [rainbow.proof :as proof]
            [rainbow.tactic :as tactic]
            [rainbow.term :as term]))

(defn base-environment []
  (let [result (persistence/load-environment "artifacts/day7/environment.edn")]
    (when-not (= :replayed (:status result))
      (throw (ex-info "Day-7 environment failed replay" {:result result})))
    (:environment result)))

(defn nat-terms [environment]
  (let [nat (inductive/constant environment 'data/Nat [])
        zero (inductive/constant environment 'data/zero [])
        successor (inductive/constant environment 'data/succ [])
        recursor (inductive/constant environment 'data/Nat.rec [inductive/type-level])
        equality (inductive/constant environment 'equality/Eq [inductive/type-level])
        reflexivity (inductive/constant environment 'equality/reflexive [inductive/type-level])
        motive (term/lambda-term nat nat)
        identity-step (term/lambda-term nat
                                        (term/lambda-term nat
                                                            (inductive/apply* successor
                                                                              (term/bound 0))))
        predecessor-step (term/lambda-term nat
                                           (term/lambda-term nat (term/bound 1)))
        one (inductive/apply* successor zero)
        two (inductive/apply* successor one)]
    {:nat nat :zero zero :successor successor :recursor recursor
     :equality equality :reflexivity reflexivity :motive motive
     :identity-step identity-step :predecessor-step predecessor-step
     :one one :two two}))

(defn identity-recursion [{:keys [recursor motive zero identity-step]} value]
  (inductive/apply* recursor motive zero identity-step value))

(defn predecessor [{:keys [recursor motive zero predecessor-step]} value]
  (inductive/apply* recursor motive zero predecessor-step value))

(defn equality-type [{:keys [equality nat]} left right]
  (inductive/apply* equality nat left right))

(defn reflexivity-proof [{:keys [reflexivity nat]} value]
  (inductive/apply* reflexivity nat value))

(defn prove-reflexive-induction [environment terms]
  (let [{:keys [nat]} terms
        target (term/pi-term nat (equality-type terms (term/bound 0) (term/bound 0)))
        introduced (tactic/run (:state (proof/start environment target)) (tactic/intro 'n))
        induced (tactic/run (:state introduced) (tactic/induction [:bound 0]))
        base (tactic/run (:state induced) (tactic/reflexivity))
        predecessor (tactic/run (:state base) (tactic/intro 'predecessor))
        hypothesis (tactic/run (:state predecessor) (tactic/intro 'induction-hypothesis))]
    (tactic/run (:state hypothesis) (tactic/reflexivity))))

(defn prove-recursor-identity [environment terms]
  (let [{:keys [nat]} terms
        target (term/pi-term
                nat
                (equality-type terms
                               (identity-recursion terms (term/bound 0))
                               (term/bound 0)))
        introduced (tactic/run (:state (proof/start environment target)) (tactic/intro 'n))
        induced (tactic/run (:state introduced) (tactic/induction [:bound 0]))
        base (tactic/run (:state induced) (tactic/reflexivity))
        predecessor (tactic/run (:state base) (tactic/intro 'predecessor))
        hypothesis (tactic/run (:state predecessor) (tactic/intro 'induction-hypothesis))
        rewritten (tactic/run (:state hypothesis)
                              (tactic/rewrite [:bound 0] {:direction :backward}))]
    (tactic/run (:state rewritten) (tactic/reflexivity))))

(defn theorem-jobs [terms]
  (let [{:keys [zero one two]} terms]
    [{:name 'nat/reflexive-induction :producer prove-reflexive-induction}
     {:name 'nat/recursor-identity :producer prove-recursor-identity}
     {:name 'nat/recursor-identity-zero
      :left (identity-recursion terms zero) :right zero}
     {:name 'nat/recursor-identity-one
      :left (identity-recursion terms one) :right one}
     {:name 'nat/recursor-identity-two
      :left (identity-recursion terms two) :right two}
     {:name 'nat/predecessor-zero
      :left (predecessor terms zero) :right zero}
     {:name 'nat/predecessor-one
      :left (predecessor terms one) :right zero}
     {:name 'nat/predecessor-two
      :left (predecessor terms two) :right one}]))

(defn register-result [environment terms job]
  (let [result (if-let [producer (:producer job)]
                 (producer environment terms)
                 {:status :proved
                  :proof {:proof/type (equality-type terms (:left job) (:right job))
                          :proof/term (reflexivity-proof terms (:right job))
                          :proof/history []}
                  :kernel :pending})]
    (when-not (= :proved (:status result))
      (throw (ex-info "Nat proof failed" {:name (:name job) :result result})))
    (let [type (or (get-in result [:proof :proof/type])
                   (equality-type terms (:left job) (:right job)))
          value (get-in result [:proof :proof/term])
          declaration-result
          (kernel/add-declaration
           environment
           {:rainbow/kind :theorem
            :rainbow/aliases #{(:name job)}
            :rainbow/universes []
            :rainbow/type type
            :rainbow/value value
            :rainbow/transparency :opaque
            :rainbow/dependencies (into (term/constants type) (term/constants value))
            :rainbow/provenance {:origin :native :producer :day-8-nat}
            :rainbow/schema-version 1})]
      (when-not (= :accepted (:status declaration-result))
        (throw (ex-info "Nat declaration rejected"
                        {:name (:name job) :result declaration-result})))
      {:environment (:environment declaration-result)
       :result result
       :declaration (:declaration declaration-result)})))

(defn build []
  (let [base (base-environment)
        terms (nat-terms base)]
    (reduce (fn [{:keys [environment results]} job]
              (let [registered (register-result environment terms job)]
                {:environment (:environment registered)
                 :results (conj results (assoc (dissoc registered :environment)
                                          :name (:name job)))}))
            {:environment base :results []}
            (theorem-jobs terms))))

(defn report []
  (let [{:keys [environment results]} (build)]
    {:status :passed
     :theorems (count results)
     :declarations (count (:rainbow.environment/declarations environment))
     :induction-proofs (count (filter #(seq (get-in % [:result :proof :proof/history])) results))
     :events (frequencies (mapcat #(map :event/tactic
                                        (get-in % [:result :proof :proof/history]))
                                  results))
     :axioms (into {} (map (fn [{:keys [name]}] [name (kernel/axioms environment name)])
                           results))}))

(defn -main [& [command path]]
  (case command
    "record" (println (pr-str (persistence/save-environment! (:environment (build)) path)))
    "replay" (let [result (persistence/load-environment path)]
               (println (pr-str (dissoc result :environment)))
               (when-not (= :replayed (:status result)) (System/exit 1)))
    (println (pr-str (report)))))
