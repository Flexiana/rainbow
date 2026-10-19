(ns rainbow.math.sums.lp-mixed-bound
  "A free-price equality block, nonnegative-price upper rows and unit upper bounds.
  Reuses equality LP and inequality LP weak duality; all rival premises are explicit."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le refl]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.equality-lp-bound :as equality]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))
(defn adjusted [c C u m w]
  (f/lam [['column nat]] (add (add (at c 'column) (lp/column C u m 'column)) (at w 'column))))
(def weak-spec
  (let [effective (adjusted 'c 'C 'u 'p 'w)
        columns (f/lam [['column nat]] (lp/column 'C 'u 'p 'column))
        cx (lp/products 'c 'x) px (lp/products columns 'x) wx (lp/products 'w 'x)
        cxpx (f/lam [['j nat]] (add (at cx 'j) (at px 'j)))
        expanded (f/lam [['j nat]] (add (at cxpx 'j) (at wx 'j)))
        dual (lp/objective 'b 'y 'm) cost (sum cx 'n) penalty (lp/objective 'd 'u 'p)
        effective-cost (lp/objective effective 'x 'n)
        split-value (add (add cost (sum px 'n)) (sum wx 'n))
        split (a/chain effective-cost
                [(sum expanded 'n) (a/sum-cong (lp/products effective 'x) expanded 'n 'j
                                     (fn [j _]
                                       (let [c (at 'c j) p (lp/column 'C 'u 'p j) w (at 'w j) x (at 'x j)]
                                         (a/ring-eq (mul (add (add c p) w) x)
                                           (add (add (mul c x) (mul p x)) (mul w x))))))]
                [(add (sum cxpx 'n) (sum wx 'n)) (call 'signed/expr-sum-value-add cxpx wx 'n)]
                [split-value (s/add-cong (sum cxpx 'n) (add cost (sum px 'n)) (sum wx 'n) (sum wx 'n)
                               (call 'signed/expr-sum-value-add cx px 'n) (refl (sum wx 'n)))])
        equality-bound (call 'signed/expr-sum-equality-lp-weak-duality 'A 'b effective 'x 'y 'm 'n 'rows 'xn 'dual)
        upper-bound (call 'signed/expr-sum-lp-weak-duality 'C 'd columns 'x 'u 'p 'n 'cuts 'xn 'un
                      (f/lam [['j nat] ['hj (s/below 'j 'n)]]
                        (call 'signed/at-most-reflexive (lp/column 'C 'u 'p 'j))))
        box-bound (a/sum-mono wx 'w 'n 'j
                    (fn [j hj]
                      (let [wj (at 'w j) xj (at 'x j)]
                        (s/le-transport (mul wj xj) (mul wj xj) (mul wj b/one) wj (refl (mul wj xj))
                          (s/trans (mul wj b/one) (mul b/one wj) wj
                            (call 'signed/multiply-commutative wj b/one)
                            (call 'signed/multiply-one-left wj))
                          (call 'signed/multiply-left-monotone wj xj b/one (at 'wn j hj) (at 'unit j hj))))))
        rhs (add (add cost penalty) (sum 'w 'n))]
    (s/spec 'signed/expr-sum-lp-mixed-upper-penalty-bound
      [['A lp/matrix] ['b family] ['C lp/matrix] ['d family] ['c family] ['x family]
       ['y family] ['u family] ['w family] ['m nat] ['p nat] ['n nat]
       ['rows (equality/equality-feasible 'A 'b 'x 'm 'n)] ['cuts (lp/primal-feasible 'C 'd 'x 'p 'n)]
       ['xn (lp/nonnegative 'x 'n)] ['unit (s/all-below 'n #(le (at 'x %) b/one))]
       ['un (lp/nonnegative 'u 'p)] ['wn (lp/nonnegative 'w 'n)]
       ['dual (b/covering-dual 'A effective 'y 'm 'n)]]
      (le dual rhs)
      (call 'signed/at-most-transitive dual split-value rhs
        (s/le-transport dual dual effective-cost split-value (refl dual) split equality-bound)
        (call 'signed/add-monotone (add cost (sum px 'n)) (add cost penalty) (sum wx 'n) (sum 'w 'n)
          (call 'signed/add-left-monotone (sum px 'n) penalty cost upper-bound) box-bound)))))
(def cancel-spec
  (s/spec 'signed/cancel-shared-addend-bound
    [['x signed] ['y signed] ['common signed] ['bound (le (add 'x 'common) (add 'y 'common))]]
    (le 'x 'y)
    (let [left (add (add 'x 'common) (a/neg 'common)) right (add (add 'y 'common) (a/neg 'common))]
      (s/le-transport left 'x right 'y (a/ring-eq left 'x) (a/ring-eq right 'y)
        (call 'signed/add-right-monotone (add 'x 'common) (add 'y 'common) (a/neg 'common) 'bound)))))
(def unit-penalty-spec
  (s/spec 'signed/unit-penalty-product
    [['size signed] ['price signed]]
    (s/eqv (mul (a/sub 'size b/one) 'price) (a/sub (mul 'size 'price) 'price))
    (let [product (mul 'size 'price) one-product (mul b/one 'price)]
      (a/chain (mul (a/sub 'size b/one) 'price)
        [(add product (mul (a/neg b/one) 'price))
         (call 'signed/multiply-distributes-add-right 'size (a/neg b/one) 'price)]
        [(a/sub product one-product)
         (s/add-cong product product (mul (a/neg b/one) 'price) (a/neg one-product)
           (refl product) (call 'signed/multiply-negate-left b/one 'price))]
        [(a/sub product 'price)
         (s/add-cong product product (a/neg one-product) (a/neg 'price)
           (refl product) (a/neg-cong one-product 'price (call 'signed/multiply-one-left 'price)))]))))
(def restore-penalty-spec
  (s/spec 'signed/restore-subtracted-penalty
    [['cost signed] ['sizes signed] ['prices signed] ['box signed]]
    (s/eqv (add (add (add 'cost (a/sub 'sizes 'prices)) 'box) 'prices)
      (add (add 'cost 'sizes) 'box))
    (a/ring-eq (add (add (add 'cost (a/sub 'sizes 'prices)) 'box) 'prices)
      (add (add 'cost 'sizes) 'box))))
(def theorem-specs [weak-spec cancel-spec unit-penalty-spec restore-penalty-spec])
(def deps '[rainbow.math.sums.equality-lp-bound rainbow.math.rational.signed.order-monotone])
(defn install [env] (support/extend-with env :expr-sum-lp-mixed-bound theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.lp-mixed-bound))
