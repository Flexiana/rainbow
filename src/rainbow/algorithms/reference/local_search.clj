(ns rainbow.algorithms.reference.local-search
  "Executable exact-rational bounded local (hill-climbing) search. A best-neighbor
  step selects the candidate maximizing the objective, keeping the current point
  on ties, so the objective never decreases. The candidate set and objective are
  pluggable; this matches the proved Rainbow definition.")

(defn best-neighbor
  "Select the candidate maximizing objective, retaining current on exact ties."
  [candidates objective current]
  (reduce (fn [best candidate]
            (if (< (objective best) (objective candidate)) candidate best))
          current
          candidates))

(defn hill-climb
  "Run a bounded number of best-neighbor steps from initial."
  [candidates objective steps initial]
  (when-not (nat-int? steps)
    (throw (ex-info "Hill-climb steps must be a natural integer" {:steps steps})))
  (nth (iterate #(best-neighbor candidates objective %) initial) steps))
