(ns rainbow.algorithms.reference.subset-sum
  "Executable subset-sum DP, matching the proved reachability OR cell.")

(defn reachable? [include-branch? exclude-branch?]
  (or include-branch? exclude-branch?))

(defn subset-sum?
  "True iff some subset of positive integers `items` sums to `target`."
  [items target]
  (let [dp (reduce
            (fn [dp item]
              (reduce (fn [dp s]
                        (assoc dp s
                               (reachable? (and (>= s item) (dp (- s item)))
                                           (dp s))))
                      dp (range target (dec item) -1)))
            (assoc (vec (repeat (inc target) false)) 0 true)
            items)]
    (dp target)))
