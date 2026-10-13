(ns rainbow.algorithms.reference.bin-packing
  "Executable first-fit bin packing, matching the proved Rainbow fit rule.")

(defn fits? [size remaining] (<= size remaining))

(defn first-fit
  "Pack items (sizes in (0,1]) into unit bins by first-fit. Returns the vector of
  bin remaining-capacities; its length is the number of bins used."
  [items]
  (reduce (fn [bins size]
            (if-let [i (first (keep-indexed
                               (fn [i r] (when (fits? size r) i)) bins))]
              (update bins i - size)
              (conj bins (- 1 size))))
          [] items))
