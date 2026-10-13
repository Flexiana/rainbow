(ns rainbow.algorithms.reference.kkt
  "Executable exact-rational KKT stationarity (AHoF O53). The stationarity
  residual matches the proved Rainbow definition; `kkt-point?` checks the
  first-order optimality conditions (stationarity, primal/dual feasibility,
  complementary slackness) for a single inequality constraint."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn stationarity
  "Lagrangian gradient residual: gradF + lambda * gradG."
  [grad-f lambda grad-g]
  (vector/add grad-f (vector/scale lambda grad-g)))

(defn kkt-point?
  "First-order KKT conditions for min f s.t. g(x) <= 0: stationarity residual is
  zero, dual feasibility lambda >= 0, primal feasibility g <= 0, and
  complementary slackness lambda * g = 0."
  [grad-f lambda grad-g g-value]
  (and (every? zero? (stationarity grad-f lambda grad-g))
       (>= lambda 0)
       (<= g-value 0)
       (zero? (* lambda g-value))))
