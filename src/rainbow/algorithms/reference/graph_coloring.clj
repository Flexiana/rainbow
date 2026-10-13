(ns rainbow.algorithms.reference.graph-coloring
  "Executable greedy graph coloring, matching the proved conflict decision.")

(defn conflict? [color-a color-b]
  (and (<= color-a color-b) (<= color-b color-a)))

(defn greedy-color
  "Greedy coloring: node -> color. adjacency is node -> neighbor set. Vertices
  colored in the given order; each gets the smallest color no neighbor uses."
  [nodes adjacency]
  (reduce
   (fn [colors v]
     (let [used (set (keep colors (adjacency v)))]
       (assoc colors v (first (remove used (range))))))
   {} nodes))

(defn proper?
  "Verify no edge joins two same-colored vertices."
  [adjacency colors]
  (not-any? (fn [[v ns]]
              (some #(and (colors %) (conflict? (colors v) (colors %))) ns))
            adjacency))
