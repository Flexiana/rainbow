(ns rainbow.algorithms.reference.r-squared
  "Executable R-squared, matching the proved Rainbow definition.")

(defn r-squared [explained-variance total-variance]
  (/ explained-variance total-variance))

(defn- mean [xs] (/ (reduce + xs) (count xs)))

(defn score
  "R-squared of predictions against targets: 1 - SS_res/SS_tot."
  [targets predictions]
  (let [my (mean targets)
        ss-tot (reduce + (map #(let [d (- % my)] (* d d)) targets))
        ss-res (reduce + (map (fn [y p] (let [d (- y p)] (* d d)))
                              targets predictions))]
    (if (zero? ss-tot) 1 (- 1 (/ ss-res ss-tot)))))
