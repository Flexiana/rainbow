(ns rainbow.algorithms.reference.pareto
  "Executable Pareto dominance and front extraction (AHoF multiobjective). The
  two-objective dominance test matches the proved Rainbow definition; the k-objective
  generalization and the non-dominated front filter build on it.")

(defn dominates?
  "Two-objective weak dominance (minimization): a is no worse in both objectives."
  [a1 a2 b1 b2]
  (and (<= a1 b1) (<= a2 b2)))

(defn dominates-vec?
  "k-objective weak dominance: a is componentwise no worse than b."
  [a b]
  (every? true? (map <= a b)))

(defn pareto-front
  "The non-dominated solutions: those not weakly dominated by any distinct other."
  [solutions]
  (vec (remove (fn [s]
                 (some (fn [o] (and (not= o s) (dominates-vec? o s))) solutions))
               solutions)))
