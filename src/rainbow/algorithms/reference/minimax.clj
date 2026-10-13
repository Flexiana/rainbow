(ns rainbow.algorithms.reference.minimax
  "Executable exact-rational minimax (AHoF adversarial decision-making). The
  two-ply value matches the proved Rainbow definition; `minimax` generalizes to
  an explicit game tree of alternating max/min plies down to scored leaves.")

(defn value
  "Two-ply minimax value: max( min(a,b), min(c,d) )."
  [a b c d]
  (max (min a b) (min c d)))

(defn minimax
  "Minimax value of an explicit game tree. A node is either a leaf {:leaf v} or a
  branch {:maximizing? bool :children [...]}. The maximizing player takes the max
  over children; the adversary takes the min."
  [node]
  (if (contains? node :leaf)
    (:leaf node)
    (let [vals (map minimax (:children node))]
      (if (:maximizing? node) (apply max vals) (apply min vals)))))
