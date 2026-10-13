(ns rainbow.algorithms.reference.k2
  "Executable exact-rational K2 structure learning (AHoF D15). The improvement
  test matches the proved Rainbow definition; `best-parents` greedily adds
  parents in the ordering while the local score improves.")

(defn improves? [new-score old-score] (<= old-score new-score))

(defn best-parents
  "K2 greedy parent selection for a node: given `candidates` (potential parents
  before the node in the ordering) and `local-score` (parents -> score), add the
  best-scoring parent while it improves; return the chosen parent set."
  [candidates local-score]
  (loop [parents #{} remaining candidates score (local-score #{})]
    (let [scored (map (fn [p] [p (local-score (conj parents p))]) remaining)
          [best gain] (when (seq scored) (apply max-key second scored))]
      (if (and best (improves? gain score) (> gain score))
        (recur (conj parents best) (remove #{best} remaining) gain)
        parents))))
