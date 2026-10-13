(ns rainbow.algorithms.reference.finite-markov-reference
  "Pure exact-rational reference operations for finite row kernels.

  This is an executable reference for certificate generation, not a proof of
  arbitrary Clojure implementations.  Formal guarantees live in the proof modules under rainbow.math and rainbow.algorithms.proofs.")

(defn row-sum [row] (reduce + row))

(defn square-kernel? [kernel]
  (and (seq kernel)
       (let [n (count kernel)]
         (every? #(= n (count %)) kernel))))

(defn normalized-kernel? [kernel]
  (and (square-kernel? kernel) (every? #(= 1 (row-sum %)) kernel)))

(defn nonnegative-mass? [mass]
  (every? #(<= 0 %) mass))

(defn step
  "Apply a finite row kernel to a mass vector using exact Clojure rationals." 
  [kernel mass]
  (assert (and (normalized-kernel? kernel)
               (= (count kernel) (count mass))
               (nonnegative-mass? mass)))
  (mapv (fn [target]
          (reduce + (map (fn [source]
                           (* (nth mass source) (get-in kernel [source target])))
                         (range (count mass)))))
        (range (count mass))))

(defn iterate [kernel steps mass]
  (nth (clojure.core/iterate #(step kernel %) mass) steps))

(defn total-mass [mass] (reduce + mass))

(defn mass-preserving? [kernel mass]
  (and (normalized-kernel? kernel)
       (= (total-mass mass) (total-mass (step kernel mass)))))

(defn total-variation [left right]
  (assert (= (count left) (count right)))
  (/ (reduce + (map #(abs (- %1 %2)) left right)) 2))

(defn stationary? [kernel mass]
  (= mass (step kernel mass)))

(defn unit-factor? [rho]
  (and (<= 0 rho) (<= rho 1)))

(defn envelope? [kernel rho steps start stationary]
  (and (unit-factor? rho)
       (normalized-kernel? kernel)
       (stationary? kernel stationary)
       (<= (total-variation (iterate kernel steps start) stationary)
           (* (reduce * 1 (repeat steps rho))
              (total-variation start stationary)))))
