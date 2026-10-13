(ns rainbow.algorithms.reference.karger
  "Executable Karger min-cut, matching the proved best-cut update.")

(defn keep-smaller-cut? [candidate current-best] (<= candidate current-best))

(defn- contract-once
  "One Karger trial with a deterministic edge order (for reproducibility), given
  edges as a vector of [u v]. Returns the resulting cut size."
  [n edges rng]
  (loop [parent (vec (range n)), edges (vec edges), remaining n]
    (letfn [(root [p x] (if (= (p x) x) x (recur p (p x))))]
      (if (<= remaining 2)
        (count (filter (fn [[u v]] (not= (root parent u) (root parent v))) edges))
        (let [[u v] (nth edges (mod (rng remaining) (count edges)))
              ru (root parent u), rv (root parent v)]
          (if (= ru rv)
            (recur parent (vec (remove #{[u v]} edges)) remaining)
            (recur (assoc parent ru rv) edges (dec remaining))))))))

(defn min-cut
  "Minimum cut estimate over `trials` Karger runs of an undirected graph."
  [n edges trials]
  (reduce (fn [best t]
            (let [c (contract-once n edges (fn [r] (+ t r)))]
              (if (keep-smaller-cut? c best) c best)))
          1000000 (range trials)))
