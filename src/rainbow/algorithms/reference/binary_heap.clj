(ns rainbow.algorithms.reference.binary-heap
  "Executable binary min-heap and heapsort, matching the proved heap-order rule.")

(defn heap-ordered? [parent child] (<= parent child))

(defn- sift-down [a i n]
  (loop [a a, i i]
    (let [l (+ (* 2 i) 1), r (+ (* 2 i) 2)
          ;; pick the smaller child: swap toward it when parent is NOT <= child
          s1 (if (and (< l n) (not (heap-ordered? (a i) (a l)))) l i)
          smallest (if (and (< r n) (not (heap-ordered? (a s1) (a r)))) r s1)]
      (if (= smallest i)
        a
        (recur (assoc a i (a smallest) smallest (a i)) smallest)))))

(defn heapsort
  "Sort ascending via a binary min-heap (heapify then repeatedly extract-min)."
  [xs]
  (let [a (vec xs), n (count a)
        heap (reduce (fn [a i] (sift-down a i n)) a (range (dec (quot n 2)) -1 -1))]
    (loop [a heap, m n, out []]
      (if (zero? m)
        out
        (let [out (conj out (a 0))
              a (assoc a 0 (a (dec m)))
              a (sift-down a 0 (dec m))]
          (recur a (dec m) out))))))
