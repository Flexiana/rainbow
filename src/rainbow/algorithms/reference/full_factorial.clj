(ns rainbow.algorithms.reference.full-factorial
  "Executable exact Full Factorial Sampling (AHoF O58). The design size matches
  the proved Rainbow definition (product of per-dimension level counts); the
  enumeration returns the Cartesian product of the per-dimension level values as
  the concrete grid of sample points.")

(defn design-size
  "Number of full-factorial sample points: product of the level counts."
  [level-counts]
  (reduce * 1 level-counts))

(defn cartesian-product
  "All sample points as the Cartesian product of the per-dimension level values."
  [level-sets]
  (reduce (fn [acc levels]
            (for [prefix acc, value levels]
              (conj prefix value)))
          [[]]
          level-sets))
