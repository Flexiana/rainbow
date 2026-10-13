(ns rainbow.algorithms.reference.forward-search
  "Executable exact-rational Forward Search (AHoF D33). The two-branch lookahead
  matches the proved Rainbow definition; `value` builds the finite-horizon
  search tree and backs up decision-node maxima to the horizon.")

(defn lookahead
  "Best of two action branches."
  [a b]
  (max a b))

(defn value
  "Finite-horizon forward-search value from `state` to `depth`. `actions` maps a
  state to [[next-state immediate-reward] ...]; at depth 0 the terminal `reward`
  is returned; a decision node takes the max over action branches."
  [actions reward depth state]
  (if (zero? depth)
    (reward state)
    (let [branches (actions state)]
      (if (empty? branches)
        (reward state)
        (apply max (map (fn [[nxt r]] (+ r (value actions reward (dec depth) nxt)))
                        branches))))))
