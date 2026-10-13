(ns rainbow.algorithms.reference.async-value-iteration
  "Executable exact reference semantics for asynchronous finite value
  iteration. The Bellman optimality backup is exactly the one used by the
  synchronous reference; only which states are refreshed each step differs. A
  schedule maps each step index to a predicate selecting the states that receive
  an optimality backup that step; every non-selected state keeps its previous
  value. Each selected state's backup reads the step's incoming value function,
  matching the proved Rainbow definition, so the selection schedule is a
  first-class pluggable strategy that shapes the trajectory."
  (:require [rainbow.algorithms.reference.value-iteration :as vi]))

(defn async-update
  "Update only the states selected by choose? with one exact optimality backup,
  preserving every non-selected state's previous value."
  [model choose? value]
  (reduce
   (fn [current state]
     (if (choose? state)
       (let [action (vi/greedy-action model value state)]
         (assoc current state (vi/action-backup model value state action)))
       current))
   value
   (:states model)))

(defn async-iterate
  "Run a bounded number of asynchronous optimality strokes under a schedule.

  `schedule` maps a step index (0-based) to a state-selection predicate. The
  reference validates the model and requires the initial value to cover every
  state with exact nonnegative rationals, matching the synchronous evaluator."
  [model schedule steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Async value-iteration steps must be a natural integer"
                    {:steps steps})))
  (let [model (vi/validate-model model)
        states (:states model)]
    (when-not (every? #(and (rational? (get initial %))
                            (not (neg? (get initial %))))
                      states)
      (throw (ex-info
              "Initial values must cover every state with exact nonnegative rationals"
              {:states states :initial initial})))
    (reduce (fn [value step] (async-update model (schedule step) value))
            initial
            (range steps))))
