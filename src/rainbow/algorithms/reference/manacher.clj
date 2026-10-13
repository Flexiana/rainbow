(ns rainbow.algorithms.reference.manacher
  "Executable longest palindromic substring (expand-around-center, matching the
  proved character-match test).")

(defn characters-match? [left-char right-char]
  (and (<= (int left-char) (int right-char)) (<= (int right-char) (int left-char))))

(defn- expand [s l r]
  (loop [l l, r r]
    (if (and (>= l 0) (< r (count s))
             (characters-match? (nth s l) (nth s r)))
      (recur (dec l) (inc r))
      [(inc l) (dec r)])))

(defn longest-palindrome
  "Longest palindromic substring of s."
  [s]
  (if (empty? s)
    ""
    (let [[bl br] (reduce (fn [[bl br] i]
                            (let [[l1 r1] (expand s i i)
                                  [l2 r2] (expand s i (inc i))
                                  [l r] (if (> (- r1 l1) (- r2 l2)) [l1 r1] [l2 r2])]
                              (if (> (- r l) (- br bl)) [l r] [bl br])))
                          [0 0] (range (count s)))]
      (subs s bl (inc br)))))
