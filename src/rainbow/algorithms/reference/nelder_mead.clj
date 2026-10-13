(ns rainbow.algorithms.reference.nelder-mead
  "Executable exact-rational Nelder-Mead simplex moves (AHoF O36). The reflection
  matches the proved Rainbow definition; expand, contract, shrink, and the
  centroid computation are the executable simplex bookkeeping."
  (:require [rainbow.algorithms.reference.finite-vector :as vector]))

(defn reflect
  "reflected = centroid + (centroid - worst)."
  [centroid worst]
  (vector/add centroid (vector/subtract centroid worst)))

(defn centroid
  "The centroid of a set of vertices (elementwise mean)."
  [vertices]
  (let [n (count vertices)]
    (mapv #(/ % n) (reduce (fn [a b] (mapv + a b)) vertices))))

(defn expand
  "expanded = centroid + gamma * (reflected - centroid)."
  [centroid reflected gamma]
  (vector/add centroid (vector/scale gamma (vector/subtract reflected centroid))))
