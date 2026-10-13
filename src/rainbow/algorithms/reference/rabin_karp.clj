(ns rainbow.algorithms.reference.rabin-karp
  "Executable Rabin-Karp string matching, matching the proved candidate decision.")

(defn candidate-match? [window-hash pattern-hash]
  (and (<= window-hash pattern-hash) (<= pattern-hash window-hash)))

(def ^:private base 256)
(def ^:private modulus 1000000007)

(defn- str-hash [s]
  (reduce (fn [h c] (mod (+ (* h base) (int c)) modulus)) 0 s))

(defn search
  "All start indices where pattern occurs in text (rolling-hash + verification)."
  [text pattern]
  (let [n (count text) m (count pattern)]
    (if (> m n)
      []
      (let [ph (str-hash pattern)
            high (reduce (fn [x _] (mod (* x base) modulus)) 1 (range (dec m)))]
        (loop [i 0, wh (str-hash (subs text 0 m)), hits []]
          (let [hits (if (and (candidate-match? wh ph)
                              (= (subs text i (+ i m)) pattern))
                       (conj hits i) hits)]
            (if (>= i (- n m))
              hits
              (let [wh (mod (+ (* (mod (- wh (* (int (nth text i)) high)) modulus)
                                 base)
                              (int (nth text (+ i m))))
                            modulus)
                    wh (mod (+ wh modulus) modulus)]
                (recur (inc i) wh hits)))))))))
