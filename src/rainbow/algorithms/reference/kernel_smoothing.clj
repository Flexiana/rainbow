(ns rainbow.algorithms.reference.kernel-smoothing
  "Executable exact-rational Kernel Smoothing VF (AHoF D26). The numerator and
  normalizer match the proved Rainbow definitions; `estimate` returns the
  kernel-weighted average value at a query.")

(defn weighted-sum [k1 v1 k2 v2] (+ (* k1 v1) (* k2 v2)))
(defn weight-total [k1 k2] (+ k1 k2))

(defn estimate
  "Kernel-weighted average value: sum(k_i v_i) / sum(k_i). `kernels` and `values`
  are aligned; returns 0 if all weights are zero."
  [kernels values]
  (let [total (reduce + 0 kernels)]
    (if (zero? total)
      0
      (/ (reduce + 0 (map * kernels values)) total))))
