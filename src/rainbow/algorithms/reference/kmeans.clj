(ns rainbow.algorithms.reference.kmeans
  "Executable 1-D k-means (Lloyd's), matching the proved Rainbow assignment.")

(defn assign [da ca db cb] (if (<= da db) ca cb))

(defn nearest-centroid
  "Index of the centroid nearest to point x (squared 1-D distance)."
  [centroids x]
  (reduce (fn [a b]
            (assign (let [d (- x (centroids a))] (* d d)) a
                    (let [d (- x (centroids b))] (* d d)) b))
          0 (range 1 (count centroids))))

(defn kmeans
  "One-dimensional k-means: iterate assignment/update to convergence, returns
  final centroids."
  [points centroids iterations]
  (nth (iterate
        (fn [cs]
          (let [groups (group-by #(nearest-centroid cs %) points)]
            (mapv (fn [i]
                    (let [g (groups i)]
                      (if (seq g) (/ (reduce + g) (count g)) (cs i))))
                  (range (count cs)))))
        (vec centroids))
       iterations))
