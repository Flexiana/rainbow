(ns rainbow.algorithms.reference.greedy-policy
  "Executable greedy policy extraction, matching the proved Rainbow definition."
  (:require [rainbow.algorithms.reference.argmax-index :as argmax-index]
            [rainbow.algorithms.reference.list-maximum :as list-maximum]))

(defn greedy-action
  "Greedy action pi(s) = argmax_a Q(s,a)."
  [q-values]
  (argmax-index/argmax-index q-values))

(defn greedy-value
  "Greedy value max_a Q(s,a)."
  [q-values]
  (list-maximum/list-maximum q-values))
