(ns rainbow.algorithms.reference.epsilon-greedy
  "Executable epsilon-greedy action selection, matching the proved Rainbow
  definition."
  (:require [rainbow.algorithms.reference.argmax-index :as argmax-index]))

(defn explores?
  "True iff the uniform draw u falls in the epsilon-band (explore)."
  [u epsilon]
  (<= u epsilon))

(defn exploit-action
  "Greedy action argmax_a Q(a)."
  [q-values]
  (argmax-index/argmax-index q-values))

(defn select-action
  "Epsilon-greedy: explore (random-action) when u <= epsilon, else exploit."
  [q-values epsilon u random-action]
  (if (explores? u epsilon) random-action (exploit-action q-values)))
