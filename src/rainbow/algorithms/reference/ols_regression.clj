(ns rainbow.algorithms.reference.ols-regression
  "Executable ordinary least squares, matching the proved Rainbow slope.")

(defn slope [covariance variance] (/ covariance variance))

(defn- mean [xs] (/ (reduce + xs) (count xs)))

(defn fit
  "Fit y = slope*x + intercept by OLS over points [x y]. Returns [slope intercept]."
  [points]
  (let [xs (map first points), ys (map second points)
        mx (mean xs), my (mean ys)
        cov (reduce + (map (fn [x y] (* (- x mx) (- y my))) xs ys))
        var (reduce + (map (fn [x] (let [d (- x mx)] (* d d))) xs))
        b (slope cov var)]
    [b (- my (* b mx))]))
