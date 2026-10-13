(ns rainbow.algorithms.reference.list-product
  "Executable product-of-list fold, matching the proved Rainbow definition.")

(defn list-product
  "Product of xs (1 for the empty list)."
  [xs]
  (reduce * 1 xs))

(defn joint-probability
  "Joint probability of independent events (product of their probabilities)."
  [probs]
  (list-product probs))
