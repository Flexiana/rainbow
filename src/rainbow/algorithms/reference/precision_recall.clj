(ns rainbow.algorithms.reference.precision-recall
  "Executable precision and recall, matching the proved Rainbow definitions.")

(defn precision [tp fp] (/ tp (+ tp fp)))
(defn recall [tp fn] (/ tp (+ tp fn)))

(defn from-confusion
  "Precision and recall from confusion-matrix counts."
  [tp fp fn]
  {:precision (precision tp fp) :recall (recall tp fn)})
