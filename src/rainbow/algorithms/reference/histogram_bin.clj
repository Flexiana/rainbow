(ns rainbow.algorithms.reference.histogram-bin
  "Executable histogram / boxcar-kernel density (AHoF). The bin count matches the
  proved Rainbow definition; `histogram` sweeps a set of bins and `density`
  normalizes a bin count into an empirical density estimate.")

(defn count-in-range
  "Number of sample values x with lo <= x <= hi."
  [lo hi xs]
  (count (filter #(and (<= lo %) (<= % hi)) xs)))

(defn histogram
  "Bin counts of xs over consecutive edges [e0 e1 e2 ...] -> counts of
  [e0,e1], [e1,e2], ..."
  [edges xs]
  (mapv (fn [[lo hi]] (count-in-range lo hi xs))
        (partition 2 1 edges)))

(defn density
  "Boxcar-kernel density estimate at a point of width w: fraction of samples
  within w of x, per unit width."
  [x w xs]
  (if (empty? xs)
    0
    (/ (count-in-range (- x w) (+ x w) xs)
       (* (count xs) (* 2 w)))))
