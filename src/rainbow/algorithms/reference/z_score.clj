(ns rainbow.algorithms.reference.z-score
  "Executable z-score standardization, matching the proved Rainbow definition.")

(defn z-score [deviation std-dev] (/ deviation std-dev))

(defn- mean [xs] (/ (reduce + xs) (count xs)))

(defn standardize
  "Standardize a value x against a sample's mean and (population) std dev."
  [xs x]
  (let [m (mean xs)
        var (/ (reduce + (map #(let [d (- % m)] (* d d)) xs)) (count xs))
        sd (Math/sqrt var)]
    (/ (- x m) sd)))
