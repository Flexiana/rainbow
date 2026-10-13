(ns rainbow.algorithms.reference.accuracy
  "Executable classification accuracy, matching the proved Rainbow definition.")

(defn accuracy [correct total] (/ correct total))

(defn score
  "Accuracy of predictions against labels."
  [labels predictions]
  (let [correct (count (filter true? (map = labels predictions)))]
    (accuracy correct (count labels))))
