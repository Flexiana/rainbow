(ns rainbow.algorithms.reference.huffman
  "Executable Huffman coding, matching the proved Rainbow definitions.")

(defn merge-frequency [f1 f2] (+ f1 f2))

(defn merge-first? [fa fb] (<= fa fb))

(defn code-lengths
  "Codeword lengths per symbol frequency via Huffman merges (returns total
  weighted length = sum over merges of merged frequency)."
  [freqs]
  (loop [nodes (sort freqs), total 0]
    (if (< (count nodes) 2)
      total
      (let [[a b & more] nodes
            m (merge-frequency a b)]
        (recur (sort (conj more m)) (+ total m))))))
