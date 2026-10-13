(ns rainbow.algorithms.reference.shooting
  "Executable Shooting Methods (AHoF V16). The trajectory simulation matches the
  proved Rainbow definition; `shoot` maps the simulation over candidate action
  sequences and returns the best-scoring plan.")

(defn simulate
  "Thread an action sequence through the dynamics from the initial state."
  [dynamics initial actions]
  (reduce dynamics initial actions))

(defn shoot
  "Shooting method: over candidate action sequences, simulate each and return the
  [plan final-state] minimizing `objective` of the resulting state."
  [dynamics initial objective candidates]
  (apply min-key (fn [[_ s]] (objective s))
         (map (fn [plan] [plan (simulate dynamics initial plan)]) candidates)))
