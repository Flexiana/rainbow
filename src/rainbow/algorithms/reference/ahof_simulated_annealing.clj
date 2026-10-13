(ns rainbow.algorithms.reference.ahof-simulated-annealing
  "Executable simulated annealing acceptance, matching the proved decision.")

(defn accepts-uphill? [u accept-probability] (<= u accept-probability))

(defn accept?
  "Accept a candidate given the objective delta (new - current, lower is better),
  temperature, and a uniform draw u."
  [delta temperature u]
  (if (<= delta 0)
    true
    (accepts-uphill? u (Math/exp (- (/ delta temperature))))))

(defn optimize
  "Minimize objective by simulated annealing from x0, using neighbor and a
  deterministic draw sequence; returns the best state seen."
  [objective neighbor x0 schedule draws]
  (loop [x x0, best x0, temps schedule, us draws]
    (if (empty? temps)
      best
      (let [t (first temps), cand (neighbor x)
            delta (- (objective cand) (objective x))
            x' (if (accept? delta t (first us)) cand x)]
        (recur x' (if (< (objective x') (objective best)) x' best)
               (rest temps) (rest us))))))
