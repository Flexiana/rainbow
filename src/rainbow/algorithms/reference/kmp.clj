(ns rainbow.algorithms.reference.kmp
  "Executable Knuth-Morris-Pratt string matching, matching the proved full-match
  decision.")

(defn matched? [matched-length pattern-length] (<= pattern-length matched-length))

(defn- failure-function [pattern]
  (let [m (count pattern)]
    (loop [f (vec (repeat m 0)), i 1, k 0]
      (if (>= i m)
        f
        (cond
          (= (pattern i) (pattern k)) (recur (assoc f i (inc k)) (inc i) (inc k))
          (pos? k) (recur f i (f (dec k)))
          :else (recur f (inc i) 0))))))

(defn search
  "All start indices where pattern occurs in text (KMP)."
  [text pattern]
  (let [text (vec text) pattern (vec pattern)
        n (count text) m (count pattern)
        f (failure-function pattern)]
    (loop [i 0, q 0, hits []]
      (if (>= i n)
        hits
        (cond
          (= (text i) (pattern q))
          (if (matched? (inc q) m)
            (recur (inc i) (f (dec m)) (conj hits (- (inc i) m)))
            (recur (inc i) (inc q) hits))
          (pos? q) (recur i (f (dec q)) hits)
          :else (recur (inc i) 0 hits))))))
