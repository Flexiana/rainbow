(ns rainbow.algorithms.reference.tabu-search
  "Executable tabu search, matching the proved tabu-membership move decision.")

(defn move-allowed? [move-is-tabu?] (not move-is-tabu?))

(defn optimize
  "Minimize objective by tabu search. neighbors returns candidate [state move]
  pairs; tenure is the tabu-list length; iters the iteration count."
  [objective neighbors x0 tenure iters]
  (loop [x x0, best x0, tabu #{}, tabu-queue [], i 0]
    (if (= i iters)
      best
      (let [cands (filter (fn [[_ move]]
                            (or (move-allowed? (contains? tabu move))
                                true))          ; aspiration handled below
                          (neighbors x))
            ;; pick best non-tabu candidate, or best overall if all tabu
            allowed (filter (fn [[_ move]] (move-allowed? (contains? tabu move)))
                            cands)
            pool (if (seq allowed) allowed cands)
            [x' move] (apply min-key (comp objective first) pool)
            tabu-queue (conj tabu-queue move)
            [tabu tabu-queue] (if (> (count tabu-queue) tenure)
                                [(disj (conj tabu move) (first tabu-queue))
                                 (subvec tabu-queue 1)]
                                [(conj tabu move) tabu-queue])]
        (recur x' (if (< (objective x') (objective best)) x' best)
               tabu tabu-queue (inc i))))))
