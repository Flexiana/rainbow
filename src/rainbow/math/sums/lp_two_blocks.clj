(ns rainbow.math.sums.lp-two-blocks
  "Weak duality with two separate constraint blocks, by two applications of the
  existing LP theorem. No interpretation of either block is assumed."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le refl]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))
(defn price [A y m B z p j] (add (lp/column A y m j) (lp/column B z p j)))
(defn dual-feasible [A y m B z p c n]
  (s/all-below n #(le (at c %) (price A y m B z p %))))
(def weak-spec
  (let [c1 (f/lam [['column nat]] (lp/column 'A 'y 'm 'column))
        c2 (f/lam [['column nat]] (lp/column 'B 'prices-B 'p 'column))
        combined (f/lam [['j nat]] (add (at c1 'j) (at c2 'j)))
        term1 (lp/products c1 'x) term2 (lp/products c2 'x)
        expanded (f/lam [['j nat]] (add (at term1 'j) (at term2 'j)))
        cx (lp/objective 'c 'x 'n) value1 (sum term1 'n) value2 (sum term2 'n)
        dual1 (lp/objective 'b 'y 'm) dual2 (lp/objective 'd 'prices-B 'p)
        weak (fn [A b y m c primal yn]
               (call 'signed/expr-sum-lp-weak-duality A b c 'x y m 'n primal 'xn yn
                 (f/lam [['j nat] ['hj (s/below 'j 'n)]]
                   (call 'signed/at-most-reflexive (lp/column A y m 'j)))))
        monotone (a/sum-mono (lp/products 'c 'x) (lp/products combined 'x) 'n 'j
                   (fn [j hj] (call 'signed/multiply-right-monotone (at 'x j) (at 'c j)
                                (price 'A 'y 'm 'B 'prices-B 'p j) (at 'xn j hj) (at 'dual j hj))))
        split (a/chain (lp/objective combined 'x 'n)
                [(sum expanded 'n) (a/sum-cong (lp/products combined 'x) expanded 'n 'j
                                     (fn [j _] (call 'signed/multiply-distributes-add-right (at c1 j) (at c2 j) (at 'x j))))]
                [(add value1 value2) (call 'signed/expr-sum-value-add term1 term2 'n)])]
    (s/spec 'signed/expr-sum-lp-two-block-weak-duality
      [['A lp/matrix] ['b family] ['B lp/matrix] ['d family] ['c family] ['x family]
       ['y family] ['prices-B family] ['m nat] ['p nat] ['n nat]
       ['rows-A (lp/primal-feasible 'A 'b 'x 'm 'n)] ['rows-B (lp/primal-feasible 'B 'd 'x 'p 'n)]
       ['xn (lp/nonnegative 'x 'n)] ['yn (lp/nonnegative 'y 'm)] ['prices-Bn (lp/nonnegative 'prices-B 'p)]
       ['dual (dual-feasible 'A 'y 'm 'B 'prices-B 'p 'c 'n)]]
      (le cx (add dual1 dual2))
      (call 'signed/at-most-transitive cx (add value1 value2) (add dual1 dual2)
        (s/le-transport cx cx (lp/objective combined 'x 'n) (add value1 value2) (refl cx) split monotone)
        (call 'signed/add-monotone value1 dual1 value2 dual2
          (weak 'A 'b 'y 'm c1 'rows-A 'yn) (weak 'B 'd 'prices-B 'p c2 'rows-B 'prices-Bn))))))
(def theorem-specs [weak-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.order-monotone])
(defn install [env] (support/extend-with env :expr-sum-lp-two-blocks theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.lp-two-blocks))
