(ns rainbow.algorithms.reference.chebyshev-scalarization
  "Executable weighted-Chebyshev (max-norm) scalarization of a multi-objective
  vector, matching the proved Rainbow definition."
  (:require [rainbow.algorithms.reference.list-maximum :as list-maximum]))

(defn scalarize
  "Max-norm scalarization of objective deviations."
  [objectives]
  (list-maximum/list-maximum objectives))

(defn weighted-scalarize
  "Weighted-Chebyshev scalarization: max of weight_i * deviation_i."
  [weights deviations]
  (scalarize (map * weights deviations)))
