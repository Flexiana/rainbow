(ns rainbow.algorithms.reference.policy-evaluation
  "Executable Bellman policy-evaluation backup, matching the proved Rainbow
  definition.")

(defn bellman-eval
  "One-step Bellman expectation backup: reward + gamma*next-value."
  [reward gamma next-value]
  (+ reward (* gamma next-value)))

(defn evaluate
  "Iterate the backup n times from an initial value estimate."
  [reward gamma n init]
  (nth (iterate #(bellman-eval reward gamma %) init) n))
