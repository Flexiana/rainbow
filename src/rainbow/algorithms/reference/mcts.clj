(ns rainbow.algorithms.reference.mcts
  "Executable MCTS UCB tree policy, matching the proved Rainbow definition."
  (:require [rainbow.algorithms.reference.list-maximum :as list-maximum]))

(defn ucb-score
  "UCB score = exploitation (mean value) + exploration bonus."
  [exploit explore]
  (+ exploit explore))

(defn tree-policy-value
  "Best (maximum) UCB score among children."
  [child-scores]
  (list-maximum/list-maximum child-scores))

(defn select-child
  "Index of the child the tree policy descends into (argmax UCB)."
  [child-scores]
  (first (apply max-key second (map-indexed vector child-scores))))
