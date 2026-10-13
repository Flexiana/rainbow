(ns rainbow.algorithms.reference.value-iteration
  "Executable exact reference semantics for finite value iteration.")

(defn- exact-nonnegative-rational? [value]
  (and (rational? value) (not (neg? value))))

(defn validate-model
  "Validate the finite executable model used by the reference evaluator.

  States and actions are ordered vectors so tie-breaking and output are
  deterministic. Transition, reward, and discount must return exact
  nonnegative Clojure rationals."
  [{:keys [states actions transition reward discount fallback] :as model}]
  (when-not (and (vector? states) (= (count states) (count (distinct states))))
    (throw (ex-info "Value-iteration states must be a duplicate-free vector"
                    {:value states})))
  (when-not (and (vector? actions) (seq actions)
                 (= (count actions) (count (distinct actions))))
    (throw (ex-info "Value-iteration actions must be a nonempty duplicate-free vector"
                    {:value actions})))
  (when-not (and (ifn? transition) (ifn? reward) (ifn? fallback))
    (throw (ex-info "Transition, reward, and fallback must be callable"
                    {:model-keys (set (keys model))})))
  (when-not (exact-nonnegative-rational? discount)
    (throw (ex-info "Discount must be an exact nonnegative rational"
                    {:discount discount})))
  (doseq [state states]
    (when-not (some #{(fallback state)} actions)
      (throw (ex-info "Fallback action is outside the action space"
                      {:state state :action (fallback state)})))
    (doseq [action actions]
      (when-not (exact-nonnegative-rational? (reward state action))
        (throw (ex-info "Reward is not an exact nonnegative rational"
                        {:state state :action action
                         :reward (reward state action)})))
      (let [masses (mapv #(transition state action %) states)]
        (when-not (every? exact-nonnegative-rational? masses)
          (throw (ex-info "Transition mass is not an exact nonnegative rational"
                          {:state state :action action :masses masses})))
        (when-not (= 1 (reduce + 0 masses))
          (throw (ex-info "Transition row is not normalized"
                          {:state state :action action :masses masses}))))))
  model)

(defn action-backup
  "Compute reward plus discounted finite expectation exactly."
  [{:keys [states transition reward discount]} value state action]
  (+ (reward state action)
     (* discount
        (reduce + 0
                (map (fn [next-state]
                       (* (transition state action next-state)
                          (get value next-state 0)))
                     states)))))

(defn greedy-action
  "Select a maximizing action, retaining the earlier action on exact ties."
  [{:keys [actions fallback] :as model} value state]
  (reduce
   (fn [best candidate]
     (if (< (action-backup model value state best)
            (action-backup model value state candidate))
       candidate
       best))
   (fallback state)
   actions))

(defn optimality-step
  "Apply one finite Bellman optimality backup to every declared state."
  [{:keys [states] :as model} value]
  (into {}
        (map (fn [state]
               (let [action (greedy-action model value state)]
                 [state (action-backup model value state action)])))
        states))

(defn value-iterate
  "Run a bounded number of exact Bellman optimality steps."
  [model steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Value-iteration steps must be a natural integer"
                    {:steps steps})))
  (let [model (validate-model model)
        states (:states model)]
    (when-not (every? #(exact-nonnegative-rational? (get initial %)) states)
      (throw (ex-info
              "Initial values must cover every state with exact nonnegative rationals"
              {:states states :initial initial})))
    (nth (iterate #(optimality-step model %) initial) steps)))
