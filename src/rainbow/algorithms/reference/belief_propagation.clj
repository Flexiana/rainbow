(ns rainbow.algorithms.reference.belief-propagation
  "Executable exact-rational Sum-Product belief propagation (AHoF D4). The message
  combination matches the proved Rainbow definition; `belief` is the normalized
  product of all incoming messages at a variable node.")

(defn combine-messages [m1 m2] (* m1 m2))

(defn belief
  "The (unnormalized) belief at a variable node: the product of all incoming
  messages, componentwise over the state values."
  [incoming-messages]
  (apply mapv * incoming-messages))

(defn normalize
  "Normalize a belief vector to sum to one (returns nil if all-zero)."
  [b]
  (let [total (reduce + 0 b)]
    (when (pos? total) (mapv #(/ % total) b))))
