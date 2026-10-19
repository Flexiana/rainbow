(ns rainbow.math.sums.lp-bounds
  "Finite covering duality and certificate-gap arithmetic, reusing the existing
  list-backed LP theorem. No integrality, positivity of matrix data, or nonempty
  dimension is assumed. Store families supply their exact feasibility premises."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(def one (f/const* 'signed/one []))
(defn covering [A b x m n] (s/all-below m #(le (at b %) (lp/row A x n %))))
(defn covering-dual [A c y m n] (s/all-below n #(le (lp/column A y m %) (at c %))))
(def cover-weak-spec
  (let [transpose (f/lam [['j nat] ['i nat]] (at 'A 'i 'j))]
    (s/spec 'signed/expr-sum-covering-weak-duality
      [['A lp/matrix] ['b family] ['c family] ['x family] ['y family] ['m nat] ['n nat]
       ['primal (covering 'A 'b 'x 'm 'n)] ['xn (lp/nonnegative 'x 'n)]
       ['yn (lp/nonnegative 'y 'm)] ['dual (covering-dual 'A 'c 'y 'm 'n)]]
      (le (lp/objective 'b 'y 'm) (lp/objective 'c 'x 'n))
      (call 'signed/expr-sum-lp-weak-duality transpose 'c 'b 'y 'x 'n 'm 'dual 'yn 'xn 'primal))))

(defn column-left [A y m j]
  (sum (f/lam [['i nat]] (mul (at y 'i) (at A 'i j))) m))
(def column-commute-spec
  (s/spec 'signed/expr-sum-column-commute
    [['A lp/matrix] ['y family] ['m nat] ['j nat]]
    (eqv (column-left 'A 'y 'm 'j) (lp/column 'A 'y 'm 'j))
    (a/sum-cong (f/lam [['i nat]] (mul (at 'y 'i) (at 'A 'i 'j)))
      (f/lam [['i nat]] (mul (at 'A 'i 'j) (at 'y 'i))) 'm 'i
      (fn [i _] (call 'signed/multiply-commutative (at 'y i) (at 'A i 'j))))))

(def unit-objective-spec
  (s/spec 'signed/expr-sum-unit-objective [['x family] ['n nat]]
    (eqv (lp/objective (f/lam [['j nat]] one) 'x 'n) (sum 'x 'n))
    (a/sum-cong (lp/products (f/lam [['j nat]] one) 'x) 'x 'n 'j
      (fn [j _] (call 'signed/multiply-one-left (at 'x j))))))

(def gap-upper-spec
  (let [left (s/add (a/sub 'dual 'primal) 'primal) right (s/add 'eps 'primal)]
    (s/spec 'signed/certificate-gap-upper-bound
      [['primal signed] ['dual signed] ['eps signed] ['gap (le (a/sub 'dual 'primal) 'eps)]]
      (le 'dual (s/add 'primal 'eps))
      (s/le-transport left 'dual right (s/add 'primal 'eps)
        (a/ring-eq left 'dual) (a/ring-eq right (s/add 'primal 'eps))
        (call 'signed/add-right-monotone (a/sub 'dual 'primal) 'eps 'primal 'gap)))))

(defn conjunction [parts]
  (if (= 1 (count parts)) (first parts)
    (call 'proposition/conjunction (first parts) (conjunction (rest parts)))))
(defn extract [parts index proof]
  (if (= 1 (count parts)) proof
    (if (zero? index) (call 'proposition/left (first parts) (conjunction (rest parts)) proof)
      (extract (rest parts) (dec index)
        (call 'proposition/right (first parts) (conjunction (rest parts)) proof)))))
(defn conjoin [parts proofs]
  (if (= 1 (count parts)) (first proofs)
    (call 'proposition/conjoin (first parts) (conjunction (rest parts)) (first proofs)
      (conjoin (rest parts) (rest proofs)))))

(def theorem-specs [cover-weak-spec column-commute-spec unit-objective-spec gap-upper-spec])
(def deps '[rainbow.math.lemmas.lp-duality rainbow.math.sums.flow-cut])
(defn install [env] (support/extend-with env :expr-sum-lp-bounds theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.lp-bounds))
