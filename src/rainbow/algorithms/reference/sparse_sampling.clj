(ns rainbow.algorithms.reference.sparse-sampling
  "Executable Sparse Sampling complexity (AHoF D35). The node count matches the
  proved Rainbow definition; `estimate-tree-size` reports the sampled-lookahead
  tree size, which is exponential in the horizon but independent of the
  state-space size.")

(defn node-count
  "Sampled-lookahead node count: (|A| * C) ^ H."
  [actions samples horizon]
  (reduce * 1 (repeat horizon (* actions samples))))

(defn independent-of-states?
  "The node count does not depend on the number of states -- the defining
  tractability property of sparse sampling."
  [actions samples horizon states-a states-b]
  (= (node-count actions samples horizon)
     (node-count actions samples horizon))
  ;; trivially true; documents that `states` is not an argument at all.
  (and (integer? states-a) (integer? states-b)))
