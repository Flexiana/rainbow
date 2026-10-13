(ns rainbow.algorithms.reference.feasibility
  "Executable constraint feasibility (AHoF constraint satisfaction / model
  checking). Feasibility matches the proved Rainbow definition; the CSP search
  returns the first feasible assignment.")

(defn feasible?
  "A candidate is feasible when all constraint truth values hold."
  [constraints]
  (every? true? constraints))

(defn solve
  "Constraint-satisfaction search: return the first candidate in `candidates`
  all of whose evaluated constraints hold, or nil if none is feasible.
  `evaluate` maps a candidate to its seq of constraint truth values."
  [evaluate candidates]
  (first (filter #(feasible? (evaluate %)) candidates)))
