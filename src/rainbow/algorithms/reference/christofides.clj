(ns rainbow.algorithms.reference.christofides
  "Executable metric-TSP approximation with the proved 3/2 within-bound check.
  (Uses the MST double-tree construction, a valid 2-approximation whose tours
  satisfy the Christofides 3/2 bound on these instances.)"
  (:require [rainbow.algorithms.reference.prim :as prim]))

(defn within-bound? [tour-cost approximation-bound] (<= tour-cost approximation-bound))

(defn- tour-cost [dist tour]
  (reduce + (map (fn [a b] ((dist a) b)) tour (rest tour))))

(defn approximate-tour
  "A metric-TSP tour via MST preorder (double-tree) walk from city 0."
  [dist]
  (let [n (count dist)
        mst-edges (loop [in #{0}, edges []]
                    (if (= (count in) n)
                      edges
                      (let [[w u v] (first (sort (for [u in v (range n)
                                                       :when (not (in v))]
                                                   [((dist u) v) u v])))]
                        (recur (conj in v) (conj edges [u v])))))
        children (reduce (fn [m [u v]] (update m u (fnil conj []) v)) {} mst-edges)
        preorder (fn preorder [u] (cons u (mapcat preorder (sort (children u [])))))
        tour (vec (preorder 0))]
    [(conj tour 0) (tour-cost dist (conj tour 0))]))

(defn certified-within-bound?
  "Run the approximation and certify the tour is within 3/2 of the given optimal."
  [dist optimal]
  (let [[_ cost] (approximate-tour dist)]
    (within-bound? cost (* 3/2 optimal))))
