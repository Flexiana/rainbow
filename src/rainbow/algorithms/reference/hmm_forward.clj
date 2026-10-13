(ns rainbow.algorithms.reference.hmm-forward
  "Executable HMM forward algorithm, matching the proved Rainbow step.")

(defn alpha-step [a0 t0 a1 t1 emission]
  (* (+ (* a0 t0) (* a1 t1)) emission))

(defn likelihood
  "Total likelihood P(obs) of an observation sequence under an n-state HMM.
  init j, trans i j, emit j o."
  [n-states obs init trans emit]
  (let [step (fn [alpha o]
               (mapv (fn [j]
                       (* (reduce (fn [s i] (+ s (* (alpha i) (trans i j))))
                                  0 (range n-states))
                          (emit j o)))
                     (range n-states)))
        alpha0 (mapv (fn [j] (* (init j) (emit j (first obs)))) (range n-states))]
    (reduce + (reduce step alpha0 (rest obs)))))
