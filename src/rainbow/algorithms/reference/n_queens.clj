(ns rainbow.algorithms.reference.n-queens
  "Executable N-Queens backtracking, matching the proved diagonal-attack test.")

(defn attacks-diagonally? [row-distance col-distance]
  (and (<= row-distance col-distance) (<= col-distance row-distance)))

(defn- safe? [queens row]
  ;; queens is a vector of chosen rows for columns 0..c-1; new column is (count queens)
  (let [c (count queens)]
    (not-any? (fn [pc]
                (or (= (queens pc) row)                       ; same row
                    (attacks-diagonally? (abs (- row (queens pc)))
                                         (abs (- c pc)))))     ; same diagonal
              (range c))))

(defn solve
  "Count the solutions to the N-queens problem."
  [n]
  (letfn [(place [queens]
            (if (= (count queens) n)
              1
              (reduce + (for [row (range n) :when (safe? queens row)]
                          (place (conj queens row))))))]
    (place [])))
