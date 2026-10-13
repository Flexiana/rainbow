(ns rainbow.algorithms.reference.qmdp
  "Executable QMDP belief-weighted value, matching the proved Rainbow
  definition.")

(defn qmdp-value
  "Belief-weighted Q-value over a two-state belief."
  [b0 q0 b1 q1]
  (+ (* b0 q0) (* b1 q1)))

(defn qmdp-action-value
  "General QMDP value: sum_s belief(s) * Q(s,a) over belief/q vectors."
  [beliefs q-values]
  (reduce + 0 (map * beliefs q-values)))
