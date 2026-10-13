(ns rainbow.algorithms.reference.adam
  "Executable exact-rational Adam optimizer core (AHoF O24). The first-moment
  update and preconditioned direction match the proved Rainbow definitions; bias
  correction and the epsilon term are the executable optimizer's concern."
  (:require [clojure.math :as math]))

(defn first-moment
  "Decayed gradient average: retain*prev + fresh*gradient."
  [retain fresh prev grad]
  (+ (* retain prev) (* fresh grad)))

(defn direction
  "Preconditioned step direction: first-moment / sqrt(second-moment) on a
  perfect-square second moment."
  [moment second-moment]
  (let [root (long (math/sqrt second-moment))]
    (assert (= second-moment (* root root)) "second moment must be a perfect square")
    (/ moment root)))
