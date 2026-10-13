(ns rainbow.math.lemmas.game-value
  "General lemmas: game value. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below all-below]]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.rational.signed.multiply-associative :as associative]
            [rainbow.math.rational.signed.order-respects :as respects]
            [rainbow.math.rational.signed.limit-uniqueness :as antisymmetric]))

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn le-resp [a ah b bh ha hb h] (call 'signed/at-most-respects-equivalence a ah b bh ha hb h))

(defn mcong [a ah b bh h k] (call 'signed/multiply-respects-equivalence a ah b bh h k))

(defn sum-cong [g h n proof] (call 'signed/expr-sum-value-respects-equivalence-below g h n proof))

(defn each [n body] (f/lam [['idx nat] ['bound (below 'idx n)]] (body 'idx 'bound)))

(defn const [c] (f/lam [['i nat]] c))

(defn column [A x m j] (sum (f/lam [['i nat]] (mul (at x 'i) (at A 'i j))) m))

(defn row [A y n i] (sum (f/lam [['j nat]] (mul (at A i 'j) (at y 'j))) n))

(defn payoff "x^T A y = sum_i x_i (A_i y)" [A x y m n]
  (sum (f/lam [['i nat]] (mul (at x 'i) (row A y n 'i))) m))

(defn column-form [A x y m n] (sum (f/lam [['j nat]] (mul (column A x m 'j) (at y 'j))) n))

(defn nonnegative [x k] (all-below k #(le s/zero (at x %))))

(defn total-one [x k] (eqv (sum x k) one))

(defn times-total-right [w k c hs]
  (trans (mul (sum w k) c) (mul one c) c
         (mcong (sum w k) one c c hs (refl c)) (call 'signed/multiply-one-left c)))

(defn times-total-left [w k c hs]
  (trans (mul c (sum w k)) (mul (sum w k) c) c
         (call 'signed/multiply-commutative c (sum w k)) (times-total-right w k c hs)))

(def upper-spec
  (let [P (payoff 'A 'x 'y 'm 'n)
        xv (sum (f/lam [['i nat]] (mul (at 'x 'i) 'v)) 'm)]
    (s/spec 'signed/game-payoff-at-most-value
            [['A matrix] ['x family] ['y family] ['v signed] ['m nat] ['n nat]
             ['rows (all-below 'm #(le (row 'A 'y 'n %) 'v))]
             ['xn (nonnegative 'x 'm)] ['xs (total-one 'x 'm)]]
            (le P 'v)
            (le-resp P P xv 'v (refl P)
                     (trans xv (mul (sum 'x 'm) 'v) 'v
                            (sym (mul (sum 'x 'm) 'v) xv (call 'signed/expr-sum-value-scale-right 'x 'v 'm))
                            (times-total-right 'x 'm 'v 'xs))
                     (call 'signed/expr-sum-value-weighted-monotone-left
                           'x (f/lam [['i nat]] (row 'A 'y 'n 'i)) (const 'v) 'm 'xn 'rows)))))

(def column-lower-spec
  (let [Q (column-form 'A 'x 'y 'm 'n)
        vy (sum (f/lam [['j nat]] (mul 'v (at 'y 'j))) 'n)
        yv (sum (f/lam [['j nat]] (mul (at (const 'v) 'j) (at 'y 'j))) 'n)]
    (s/spec 'signed/game-value-at-most-column-form
            [['A matrix] ['x family] ['y family] ['v signed] ['m nat] ['n nat]
             ['columns (all-below 'n #(le 'v (column 'A 'x 'm %)))]
             ['yn (nonnegative 'y 'n)] ['ys (total-one 'y 'n)]]
            (le 'v Q)
            (le-resp yv 'v Q Q
                     (trans vy (mul 'v (sum 'y 'n)) 'v
                            (sym (mul 'v (sum 'y 'n)) vy (call 'signed/expr-sum-value-scale-left 'y 'v 'n))
                            (times-total-left 'y 'n 'v 'ys))
                     (refl Q)
                     (call 'signed/expr-sum-value-weighted-monotone-right
                           'y (const 'v) (f/lam [['j nat]] (column 'A 'x 'm 'j)) 'n 'yn 'columns)))))

(def swap-spec
  (let [inner (fn [i j] (mul (mul (at 'x i) (at 'A i j)) (at 'y j)))
        s1 (sum (f/lam [['i nat]] (sum (f/lam [['j nat]] (mul (at 'x 'i) (mul (at 'A 'i 'j) (at 'y 'j)))) 'n)) 'm)
        s2 (sum (f/lam [['i nat]] (sum (f/lam [['j nat]] (inner 'i 'j)) 'n)) 'm)
        s3 (sum (f/lam [['j nat]] (sum (f/lam [['i nat]] (inner 'i 'j)) 'm)) 'n)
        P (payoff 'A 'x 'y 'm 'n) Q (column-form 'A 'x 'y 'm 'n)]
    (s/spec 'signed/game-payoff-column-form
            [['A matrix] ['x family] ['y family] ['m nat] ['n nat]]
            (eqv P Q)
            (trans P s1 Q
                   (sum-cong (f/lam [['i nat]] (mul (at 'x 'i) (row 'A 'y 'n 'i)))
                             (f/lam [['i nat]] (sum (f/lam [['j nat]] (mul (at 'x 'i) (mul (at 'A 'i 'j) (at 'y 'j)))) 'n)) 'm
                             (each 'm (fn [i _] (call 'signed/expr-sum-value-scale-left
                                                      (f/lam [['j nat]] (mul (at 'A i 'j) (at 'y 'j))) (at 'x i) 'n))))
                   (trans s1 s2 Q
                          (sum-cong (f/lam [['i nat]] (sum (f/lam [['j nat]] (mul (at 'x 'i) (mul (at 'A 'i 'j) (at 'y 'j)))) 'n))
                                    (f/lam [['i nat]] (sum (f/lam [['j nat]] (inner 'i 'j)) 'n)) 'm
                                    (each 'm (fn [i _]
                                               (sum-cong (f/lam [['j nat]] (mul (at 'x i) (mul (at 'A i 'j) (at 'y 'j))))
                                                         (f/lam [['j nat]] (inner i 'j)) 'n
                                                         (f/lam [['jdx nat] ['jbound (below 'jdx 'n)]]
                                                                (sym (inner i 'jdx) (mul (at 'x i) (mul (at 'A i 'jdx) (at 'y 'jdx)))
                                                                     (call 'signed/multiply-associative (at 'x i) (at 'A i 'jdx) (at 'y 'jdx))))))))
                          (trans s2 s3 Q
                                 (call 'signed/expr-sum-value-swap (f/lam [['i nat] ['j nat]] (inner 'i 'j)) 'n 'm)
                                 (sum-cong (f/lam [['j nat]] (sum (f/lam [['i nat]] (inner 'i 'j)) 'm))
                                           (f/lam [['j nat]] (mul (column 'A 'x 'm 'j) (at 'y 'j))) 'n
                                           (each 'n (fn [j _]
                                                      (sym (mul (column 'A 'x 'm j) (at 'y j))
                                                           (sum (f/lam [['i nat]] (inner 'i j)) 'm)
                                                           (call 'signed/expr-sum-value-scale-right
                                                                 (f/lam [['i nat]] (mul (at 'x 'i) (at 'A 'i j))) (at 'y j) 'm)))))))))))

(def lower-spec
  (let [P (payoff 'A 'x 'y 'm 'n) Q (column-form 'A 'x 'y 'm 'n)]
    (s/spec 'signed/game-value-at-most-payoff
            [['A matrix] ['x family] ['y family] ['v signed] ['m nat] ['n nat]
             ['columns (all-below 'n #(le 'v (column 'A 'x 'm %)))]
             ['yn (nonnegative 'y 'n)] ['ys (total-one 'y 'n)]]
            (le 'v P)
            (le-resp 'v 'v Q P (refl 'v)
                     (sym P Q (call 'signed/game-payoff-column-form 'A 'x 'y 'm 'n))
                     (call 'signed/game-value-at-most-column-form 'A 'x 'y 'v 'm 'n 'columns 'yn 'ys)))))

(def saddle-binders
  [['A matrix] ['x family] ['y family] ['v signed] ['m nat] ['n nat]
   ['xn (nonnegative 'x 'm)] ['xs (total-one 'x 'm)]
   ['yn (nonnegative 'y 'n)] ['ys (total-one 'y 'n)]
   ['columns (all-below 'n #(le 'v (column 'A 'x 'm %)))]
   ['rows (all-below 'm #(le (row 'A 'y 'n %) 'v))]])

(def value-spec
  (let [P (payoff 'A 'x 'y 'm 'n)]
    (s/spec 'signed/game-payoff-equivalent-value saddle-binders (eqv P 'v)
            (call 'signed/at-most-antisymmetric P 'v
                  (call 'signed/game-payoff-at-most-value 'A 'x 'y 'v 'm 'n 'rows 'xn 'xs)
                  (call 'signed/game-value-at-most-payoff 'A 'x 'y 'v 'm 'n 'columns 'yn 'ys)))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [parts i proof]
  (if (= 1 (count parts)) proof
      (if (zero? i) (call 'proposition/left (first parts) (conjunction (rest parts)) proof)
          (extract (rest parts) (dec i)
                   (call 'proposition/right (first parts) (conjunction (rest parts)) proof)))))

(def theorem-specs [upper-spec column-lower-spec swap-spec lower-spec value-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      s/extend-environment
      units/extend-environment
      associative/extend-environment
      respects/extend-environment
      antisymmetric/extend-environment
      (support/extend-with :expr-sum-game-value theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
