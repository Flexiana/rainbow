(ns rainbow.algorithms.reference.activity-selection
  "Executable greedy activity selection, matching the proved Rainbow rule.")

(defn compatible? [start last-finish] (<= last-finish start))

(defn select-activities
  "Maximum compatible set by earliest-finish-time greedy. Activities are
  [start finish]. Returns the chosen activities in order."
  [activities]
  (loop [acts (sort-by second activities), last-finish 0, chosen []]
    (if (empty? acts)
      chosen
      (let [[s f :as a] (first acts)]
        (if (compatible? s last-finish)
          (recur (rest acts) f (conj chosen a))
          (recur (rest acts) last-finish chosen))))))
