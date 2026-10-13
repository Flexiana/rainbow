(ns rainbow.algorithms.reference.interior-point
  "Executable exact-rational Interior Point / Barrier method (AHoF O50). The
  rational inverse-barrier objective matches the proved Rainbow definition; the
  mu-shrinking schedule and the log-barrier variant are executable concerns."
  (:refer-clojure :exclude []))

(defn barrier-objective
  "objective + mu / slack (rational inverse barrier)."
  [objective mu slack]
  (+ objective (/ mu slack)))
