(ns rainbow.proof
  "Immutable proof states and kernel-checked terminal reconstruction."
  (:require [rainbow.canonical :as canonical]
            [rainbow.environment :as environment]
            [rainbow.kernel :as kernel]
            [rainbow.term :as term]))

(defn hole [id] [:hole id])
(defn hole? [value] (and (vector? value) (= :hole (first value)) (= 2 (count value))))

(defn replace-hole [partial id replacement]
  (cond
    (= partial (hole id)) replacement
    (not (vector? partial)) partial
    :else (mapv #(replace-hole % id replacement) partial)))

(defn contains-holes? [partial]
  (cond
    (hole? partial) true
    (vector? partial) (boolean (some contains-holes? partial))
    :else false))

(defn term-axioms
  "Computes the explicit transitive axiom closure of a proof term."
  [checked-environment proof-term]
  (reduce
   (fn [result id]
     (if-let [declaration (environment/declaration checked-environment id)]
       (cond-> (into result (:rainbow/axioms declaration))
         (= :axiom (:rainbow/kind declaration)) (conj id))
       result))
   #{}
   (term/constants proof-term)))

(defn close-over-context
  "Abstracts an open term over an innermost-first local context."
  [context expression constructor]
  (reduce (fn [body {:goal/keys [type mode]}]
            (constructor type body (or mode :explicit)))
          expression
          context))

(defn check-in-context
  ([environment context expression expected]
   (check-in-context environment context expression expected #{}))
  ([environment context expression expected universe-parameters]
   (kernel/check environment
                 (close-over-context context expression term/lambda-term)
                 (close-over-context context expected term/pi-term)
                 universe-parameters)))

(defn infer-in-context [environment context expression universe-parameters]
  (let [closed (close-over-context context expression term/lambda-term)
        result (kernel/infer environment closed universe-parameters)]
    (if-not (= :checked (:status result))
      result
      (loop [type (:type result)
             remaining (count context)]
        (if (zero? remaining)
          {:status :checked :type type}
          (let [head (if (= :pi (first type))
                       type
                       (:term (kernel/normalize environment type)))]
            (if (= :pi (first head))
              (recur (nth head 2) (dec remaining))
              {:status :rejected
               :error {:error/category :proof/context-inference-failed
                       :type type}})))))))

(defn session-id [environment target context universes]
  (canonical/content-id
   {:environment (environment/environment-id environment)
    :target target
    :context (mapv :goal/type context)
    :universes (vec (sort-by str universes))}))

(defn start
  ([environment target] (start environment target {}))
  ([environment target {:keys [context names universes]
                        :or {context [] names [] universes []}}]
   (let [context (mapv (fn [index type]
                         {:goal/name (or (nth names index nil)
                                         (symbol (str "h" index)))
                          :goal/type type
                          :goal/mode :explicit})
                       (range)
                       context)
         target-check (if (empty? context)
                        (kernel/infer environment target (set universes))
                        (kernel/infer environment
                                      (close-over-context context target term/pi-term)
                                      (set universes)))
         target-kind (when (= :checked (:status target-check))
                       (:term (kernel/normalize environment (:type target-check))))]
     (if-not (and (= :checked (:status target-check))
                  (= :sort (first target-kind)))
       {:status :rejected
        :error {:error/category :proof/invalid-target
                :cause target-check}}
       (let [root-id (session-id environment target context universes)]
         {:status :ready
          :state {:rainbow/kind :proof-state
                  :proof/schema-version 1
                  :proof/session-id root-id
                  :proof/environment environment
                  :proof/root-goal target
                  :proof/root-context context
                  :proof/universes (set universes)
                  :proof/goals [{:goal/id "g-0"
                                 :goal/context context
                                 :goal/target target
                                 :goal/path []}]
                  :proof/partial-term (hole "g-0")
                  :proof/next-id 1
                  :proof/history []
                  :proof/attempted #{}
                  :proof/metrics {:kernel-checks 1 :branches 0}}})))))

(defn current-goal [state]
  (first (:proof/goals state)))

(defn fresh-goal-id [state]
  (str "g-" (:proof/next-id state)))

(defn fail-result [state tactic category detail]
  {:status :failure
   :state state
   :failure {:failure/category category
             :failure/tactic tactic
             :failure/detail detail}})

(defn progress
  "Replaces the focused goal and either returns a new state or kernel-checks a terminal term."
  [state replacement new-goals event]
  (let [focused (current-goal state)
        updated (-> state
                    (assoc :proof/partial-term
                           (replace-hole (:proof/partial-term state)
                                         (:goal/id focused)
                                         replacement))
                    (assoc :proof/goals
                           (into (vec new-goals) (rest (:proof/goals state))))
                    (update :proof/next-id + (count new-goals))
                    (update :proof/history conj event)
                    (update-in [:proof/metrics :kernel-checks] (fnil inc 0)))]
    (if (seq (:proof/goals updated))
      {:status :progress :state updated :goals (:proof/goals updated) :event event}
      (if (contains-holes? (:proof/partial-term updated))
        (fail-result state (:event/tactic event) :proof/orphan-hole
                     {:partial-term (:proof/partial-term updated)})
        (let [environment (:proof/environment state)
              proof-term (:proof/partial-term updated)
              expected (close-over-context (:proof/root-context state)
                                           (:proof/root-goal state)
                                           term/pi-term)
              closed-proof (close-over-context (:proof/root-context state)
                                               proof-term
                                               term/lambda-term)
              checked (kernel/check environment closed-proof expected
                                    (:proof/universes state))]
          (if (= :checked (:status checked))
            {:status :proved
             :proof {:rainbow/kind :checked-proof
                     :proof/term closed-proof
                     :proof/type expected
                     :proof/environment-id (environment/environment-id environment)
                     :proof/axioms (term-axioms environment closed-proof)
                     :proof/history (:proof/history updated)}
             :state updated
             :kernel checked
             :event event}
            (fail-result state (:event/tactic event) :proof/kernel-rejected-terminal
                         {:kernel checked})))))))
