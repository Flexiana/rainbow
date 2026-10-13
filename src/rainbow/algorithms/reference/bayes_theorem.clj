(ns rainbow.algorithms.reference.bayes-theorem
  "Executable Bayes' theorem, matching the proved Rainbow definition.")

(defn posterior
  "P(H|E) = P(E|H) P(H) / P(E)."
  [likelihood prior evidence]
  (/ (* likelihood prior) evidence))

(defn posterior-from-marginals
  "Posterior P(H|E) from likelihood P(E|H), prior P(H), and false-positive
  P(E|not-H); evidence = P(E|H)P(H) + P(E|not-H)(1-P(H))."
  [likelihood prior false-positive]
  (let [evidence (+ (* likelihood prior) (* false-positive (- 1 prior)))]
    (posterior likelihood prior evidence)))
