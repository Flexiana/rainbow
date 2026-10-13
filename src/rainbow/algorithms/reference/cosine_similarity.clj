(ns rainbow.algorithms.reference.cosine-similarity
  "Executable cosine similarity, matching the proved Rainbow definition.")

(defn cosine [dot-product magnitude-product] (/ dot-product magnitude-product))

(defn- dot [a b] (reduce + (map * a b)))
(defn- magnitude [v] (Math/sqrt (dot v v)))

(defn similarity
  "Cosine similarity of two vectors."
  [a b]
  (let [mp (* (magnitude a) (magnitude b))]
    (if (zero? mp) 0 (cosine (dot a b) mp))))
