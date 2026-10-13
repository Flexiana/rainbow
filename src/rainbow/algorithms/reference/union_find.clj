(ns rainbow.algorithms.reference.union-find
  "Executable union-find connectivity, matching the proved Rainbow definition.")

(defn connected?
  "True iff two representatives are equal (same set)."
  [ra rb]
  (and (<= ra rb) (<= rb ra)))

(defn find-rep
  "Representative of x under a parent map (path to a root)."
  [parent x]
  (loop [x x] (if (= (parent x) x) x (recur (parent x)))))
