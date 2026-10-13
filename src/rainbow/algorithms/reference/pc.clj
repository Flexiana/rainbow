(ns rainbow.algorithms.reference.pc
  "Executable exact-rational PC algorithm (AHoF D16). The independence test
  matches the proved Rainbow definition; `skeleton` removes edges whose endpoints
  are found conditionally independent.")

(defn independent? [statistic threshold] (<= statistic threshold))

(defn skeleton
  "Undirected skeleton: keep an edge [x y] only if no conditioning set makes its
  endpoints independent. `stat-of` maps [x y] to its dependence statistic."
  [edges stat-of threshold]
  (vec (remove (fn [e] (independent? (stat-of e) threshold)) edges)))
