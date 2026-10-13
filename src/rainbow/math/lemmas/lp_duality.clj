(ns rainbow.math.lemmas.lp-duality
  "General lemmas: lp duality. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed zero family call at sum mul le eqv refl sym]]
            [rainbow.math.rational.signed.lp-duality-on :as lp]))

(def matrix (f/arrow nat family))

(defn products [a x] (f/lam [['z nat]] (mul (at a 'z) (at x 'z))))

(defn objective [c x n] (sum (products c x) n))

(defn row [A x n i] (sum (f/lam [['j nat]] (mul (at A i 'j) (at x 'j))) n))

(defn column [A y m j] (sum (f/lam [['i nat]] (mul (at A 'i j) (at y 'i))) m))

(defn primal-feasible [A b x m n] (s/all-below m #(le (row A x n %) (at b %))))

(defn dual-feasible [A c y m n] (s/all-below n #(le (at c %) (column A y m %))))

(defn nonnegative [x n] (s/all-below n #(le zero (at x %))))

(defn list-bounds [F G n H] (call 'signed/expr-sum-bounds-as-list F G n H))

(def weak-duality-spec
  (let [binders [['A matrix] ['b family] ['c family] ['x family] ['y family] ['m nat] ['n nat]
                 ['primal (primal-feasible 'A 'b 'x 'm 'n)] ['xn (nonnegative 'x 'n)]
                 ['yn (nonnegative 'y 'm)] ['dual (dual-feasible 'A 'c 'y 'm 'n)]]
        row-f (fn [i] (f/lam [['j nat]] (mul (at 'A i 'j) (at 'x 'j))))
        col-f (fn [j] (f/lam [['i nat]] (mul (at 'A 'i j) (at 'y 'i))))
        rows (f/lam [['ri nat]] (s/map-sum (row-f 'ri) 'n))
        cols (f/lam [['cj nat]] (s/map-sum (col-f 'cj) 'm))
        z (f/lam [['i nat]] zero)
        pc (products 'c 'x) dc (products 'b 'y)
        hp (f/lam [['idx nat] ['bound (s/below 'idx 'm)]]
                  (s/le-transport (sum (row-f 'idx) 'n) (s/map-sum (row-f 'idx) 'n)
                                  (at 'b 'idx) (at 'b 'idx)
                                  (s/bridge (row-f 'idx) 'n) (refl (at 'b 'idx))
                                  (at 'primal 'idx 'bound)))
        hd (f/lam [['idx nat] ['bound (s/below 'idx 'n)]]
                  (s/le-transport (at 'c 'idx) (at 'c 'idx)
                                  (sum (col-f 'idx) 'm) (s/map-sum (col-f 'idx) 'm)
                                  (refl (at 'c 'idx)) (s/bridge (col-f 'idx) 'm)
                                  (at 'dual 'idx 'bound)))]
    (s/spec 'signed/expr-sum-lp-weak-duality binders
            (le (objective 'c 'x 'n) (objective 'b 'y 'm))
            (s/le-transport (s/map-sum pc 'n) (sum pc 'n) (s/map-sum dc 'm) (sum dc 'm)
                            (sym (sum pc 'n) (s/map-sum pc 'n) (s/bridge pc 'n))
                            (sym (sum dc 'm) (s/map-sum dc 'm) (s/bridge dc 'm))
                            (f/app (f/const* 'optimization/signed-lp-weak-duality-on [[:zero]])
                                   nat nat 'A 'b 'c 'x 'y (s/indices 'm) (s/indices 'n)
                                   (list-bounds rows 'b 'm hp) (list-bounds 'c cols 'n hd)
                                   (list-bounds z 'x 'n 'xn) (list-bounds z 'y 'm 'yn))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [parts i proof]
  (if (= 1 (count parts)) proof
      (if (zero? i) (call 'proposition/left (first parts) (conjunction (rest parts)) proof)
          (extract (rest parts) (dec i)
                   (call 'proposition/right (first parts) (conjunction (rest parts)) proof)))))

(def theorem-specs [weak-duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      s/extend-environment
      lp/extend-environment
      (support/extend-with :expr-sum-lp-duality theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
