(ns rainbow.algorithms.reference.branch-and-bound
  "Executable exact-rational Branch and Bound bounding (AHoF D34). The domination
  test matches the proved Rainbow definition (maximization convention: a node is
  dominated when its optimistic upper bound cannot exceed the incumbent). The
  branching and bound functions are pluggable; here we expose the pruning
  operation over a frontier of nodes.")

(defn dominated?
  "A node is dominated when its optimistic upper bound is at most the incumbent,
  so its subtree cannot contain anything better than the incumbent."
  [upper-bound incumbent]
  (<= upper-bound incumbent))

(defn prune-frontier
  "Keep only the nodes whose upper bound could still beat the incumbent; drop the
  dominated ones. `bound-fn` maps a node to its optimistic upper bound."
  [incumbent nodes bound-fn]
  (vec (remove #(dominated? (bound-fn %) incumbent) nodes)))

(defn best-leaf-value
  "Maximization B&B over an explicit tree. `children` maps a node to child nodes
  (empty for leaves); `upper-bound` is an admissible optimistic bound; `value`
  scores leaves. Prunes any subtree whose bound cannot beat the running best."
  [children upper-bound value root]
  (let [incumbent (atom nil)]
    (letfn [(explore [node]
              (when-not (and (some? @incumbent)
                             (dominated? (upper-bound node) @incumbent))
                (let [kids (children node)]
                  (if (empty? kids)
                    (let [v (value node)]
                      (when (or (nil? @incumbent) (> v @incumbent))
                        (reset! incumbent v)))
                    (doseq [child kids] (explore child))))))]
      (explore root)
      @incumbent)))
