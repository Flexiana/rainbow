(ns rainbow.algorithms.reference.sat
  "Executable SAT-based bounded model checking (AHoF V50). Clause satisfaction
  matches the proved Rainbow definition; a CNF formula is satisfied when every
  clause is, and a bounded model check searches assignments for a counterexample.")

(defn clause-satisfied?
  "A clause (seq of literal truth values) is satisfied if any literal is true."
  [literals]
  (boolean (some true? literals)))

(defn formula-satisfied?
  "A CNF formula (seq of clauses) is satisfied when every clause is."
  [clauses]
  (every? clause-satisfied? clauses))

(defn satisfying-assignment
  "Search variable assignments (maps of var->bool over `vars`) for one that
  satisfies `clauses-of` (an assignment -> seq-of-clauses encoder). Returns the
  first satisfying assignment or nil (UNSAT within the bound)."
  [vars clauses-of]
  (letfn [(assignments [vs]
            (if (empty? vs)
              [{}]
              (for [a (assignments (rest vs)), b [true false]]
                (assoc a (first vs) b))))]
    (first (filter #(formula-satisfied? (clauses-of %)) (assignments vars)))))
