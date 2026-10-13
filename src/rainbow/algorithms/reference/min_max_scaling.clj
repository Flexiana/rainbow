(ns rainbow.algorithms.reference.min-max-scaling
  "Executable min-max scaling, matching the proved Rainbow definition.")

(defn scaled [offset range] (/ offset range))

(defn normalize
  "Scale every value of xs into [0,1] by min-max scaling."
  [xs]
  (let [lo (apply min xs) hi (apply max xs) r (- hi lo)]
    (if (zero? r) (mapv (constantly 0) xs) (mapv #(scaled (- % lo) r) xs))))
