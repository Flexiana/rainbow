(ns rainbow.algorithms.reference.hungarian
  "Executable assignment problem, matching the proved tight-cell decision.")

(defn tight? [reduced-cost] (<= reduced-cost 0))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (vec coll))
    (mapcat (fn [x]
              (map #(vec (cons x %)) (permutations (remove #{x} coll))))
            coll)))

(defn- reduce-rows [cost]
  (mapv (fn [row] (let [m (apply min row)] (mapv #(- % m) row))) cost))

(defn min-cost-assignment
  "Minimum total cost of a perfect assignment for a square cost matrix (exact via
  permutation search; the Hungarian method computes the same in O(n^3))."
  [cost]
  (let [n (count cost)]
    (apply min (for [perm (permutations (range n))]
                 (reduce + (map (fn [i j] ((cost i) j)) (range n) perm))))))

(defn assignable-cells
  "Cells that are tight (zero reduced cost) after row reduction."
  [cost]
  (let [rc (reduce-rows cost)]
    (set (for [i (range (count rc)) j (range (count (rc i)))
               :when (tight? ((rc i) j))]
           [i j]))))
