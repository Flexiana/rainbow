(ns rainbow.algorithms.reference.dbscan
  "Executable DBSCAN clustering, matching the proved Rainbow core-point rule.")

(defn is-core? [neighbor-count min-pts] (<= min-pts neighbor-count))

(defn- neighbors [points eps i]
  (filter #(<= (abs (- (points i) (points %))) eps) (range (count points))))

(defn dbscan
  "1-D DBSCAN. Returns a cluster id per point (-1 = noise)."
  [points eps min-pts]
  (let [n (count points)]
    (loop [i 0, cid 0, labels (vec (repeat n nil))]
      (if (= i n)
        (mapv #(or % -1) labels)
        (if (or (labels i) (not (is-core? (count (neighbors points eps i)) min-pts)))
          (recur (inc i) cid labels)
          (let [labels (loop [seeds (vec (neighbors points eps i))
                              labels (assoc labels i cid)]
                         (if (empty? seeds)
                           labels
                           (let [q (peek seeds), seeds (pop seeds)]
                             (if (labels q)
                               (recur seeds labels)
                               (let [labels (assoc labels q cid)
                                     qn (neighbors points eps q)]
                                 (recur (if (is-core? (count qn) min-pts)
                                          (into seeds qn) seeds)
                                        labels))))))]
            (recur (inc i) (inc cid) labels)))))))
