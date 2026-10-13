(ns rainbow.algorithms.reference.concrete-reachability
  "Executable Concrete Reachability (AHoF V44). The one-step forward image matches
  the proved Rainbow definition; `reachable` iterates it to trace the concrete
  reachable set out to a horizon.")

(defn reach-step
  "One-step forward image: apply the transition to every state."
  [step states]
  (mapv step states))

(defn reachable
  "Concrete reachable states after `horizon` steps from `initial`, deduplicated."
  [step initial horizon]
  (nth (iterate (fn [states] (vec (distinct (reach-step step states)))) initial)
       horizon))
