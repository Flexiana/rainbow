(ns rainbow.algorithms.reference.rollout
  "Executable exact-rational Rollout with Heuristic (AHoF D32). The trajectory
  return matches the proved Rainbow definition; `estimate-value` averages the
  returns of several simulated rollouts.")

(defn trajectory-return
  "Undiscounted two-step return."
  [r1 r2]
  (+ r1 r2))

(defn simulate-return
  "Discounted return of a reward sequence at discount factor `gamma`."
  [rewards gamma]
  (reduce + 0 (map-indexed (fn [t r] (* r (reduce * 1 (repeat t gamma)))) rewards)))

(defn estimate-value
  "Rollout value estimate: mean discounted return over `n` simulated reward
  sequences produced by `simulate`."
  [simulate gamma n]
  (if (zero? n)
    0
    (/ (reduce + 0 (map (fn [_] (simulate-return (simulate) gamma)) (range n)))
       n)))
