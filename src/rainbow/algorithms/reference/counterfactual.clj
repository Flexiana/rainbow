(ns rainbow.algorithms.reference.counterfactual
  "Executable exact-rational Counterfactual Explanation proximity (AHoF V57).
  The squared distance matches the proved Rainbow definition; the desired-class
  penalty and the outer minimization are the executable concern."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]
            [rainbow.algorithms.reference.inner-product :as inner]))

(defn distance-squared
  "Squared distance between original and candidate: <o-c, o-c>."
  [original candidate]
  (let [d (vector/subtract original candidate)]
    (inner/dot d d)))

(defn score
  "Counterfactual objective: distance-squared + weight * class-penalty."
  [original candidate weight class-penalty]
  (+ (distance-squared original candidate) (* weight class-penalty)))
