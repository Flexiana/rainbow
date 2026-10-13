(ns rainbow.algorithms.reference.penalty-method
  "Executable exact-rational Penalty Method (AHoF O48). The augmented objective
  matches the proved Rainbow definition; the constraint functions and the
  rho-growing schedule are the executable optimizer's concern."
  (:refer-clojure :exclude [max]))

(defn augmented
  "augmented = objective + rho * penalty."
  [objective rho penalty]
  (+ objective (* rho penalty)))

(defn violation
  "A one-sided inequality penalty: max(0, g)^2, zero when the constraint g <= 0
  holds."
  [g]
  (let [v (clojure.core/max 0 g)] (* v v)))
