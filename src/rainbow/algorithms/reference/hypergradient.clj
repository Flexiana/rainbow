(ns rainbow.algorithms.reference.hypergradient
  "Executable exact-rational Hypergradient Descent (AHoF O25). The learning-rate
  update matches the proved Rainbow definition; the base parameter update is the
  wrapped optimizer's concern."
  (:require [rainbow.algorithms.reference.inner-product :as inner]))

(defn update-rate
  "rate' = rate + beta * <g_current, g_previous>."
  [rate beta g-current g-previous]
  (+ rate (* beta (inner/dot g-current g-previous))))
