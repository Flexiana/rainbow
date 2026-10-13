(ns rainbow.algorithms.reference.viterbi
  "Executable Viterbi decoding, matching the proved Rainbow cell recurrence.")

(defn path-prob [prev transition emission] (* prev transition emission))

(defn cell [current-best candidate]
  (if (<= current-best candidate) candidate current-best))

(defn decode
  "Most-likely state sequence probability for an HMM. states, obs are counts;
  init j = P(state j), trans i j, emit j o. Returns the best final path prob."
  [n-states obs init trans emit]
  (let [step (fn [delta o]
               (mapv (fn [j]
                       (reduce (fn [best i]
                                 (cell best (path-prob (delta i) (trans i j)
                                                       (emit j o))))
                               0 (range n-states)))
                     (range n-states)))
        delta0 (mapv (fn [j] (* (init j) (emit j (first obs)))) (range n-states))]
    (apply max (reduce step delta0 (rest obs)))))
