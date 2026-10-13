(ns rainbow.algorithms.reference.fibonacci
  "Executable Fibonacci numbers (AHoF). The linear-pass recurrence matches the
  proved Rainbow definition; `fib-search-probes` reports the Fibonacci-ratio
  probe offsets used by Fibonacci line search.")

(defn fib
  "The n-th Fibonacci number, computed in one linear pass."
  [n]
  (first (nth (iterate (fn [[a b]] [b (+ a b)]) [0 1]) n)))

(defn fib-search-probes
  "The two interior probe positions of Fibonacci search on [lo, hi] with n
  intervals: they split the range at consecutive Fibonacci ratios."
  [lo hi n]
  (let [width (- hi lo)]
    [(+ lo (* width (/ (fib n) (fib (+ n 2)))))
     (+ lo (* width (/ (fib (+ n 1)) (fib (+ n 2)))))]))
