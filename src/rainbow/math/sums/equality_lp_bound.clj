(ns rainbow.math.sums.equality-lp-bound
  "Weak duality for equality rows and unrestricted dual prices. Reuses the
  existing bilinear-swap theorem; only the rival variables must be nonnegative."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.dea-efficiency :as dea]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(defn equality-feasible [A rhs x m n]
  (s/all-below m #(eqv (lp/row A x n %) (at rhs %))))
(def weak-spec
  (let [A 'A x 'x y 'y m 'm n 'n
        row-left (fn [i] (sum (f/lam [['j nat]] (mul (at x 'j) (at A i 'j))) n))
        L (f/lam [['i nat]] (mul (at y 'i) (row-left 'i)))
        R (f/lam [['j nat]] (mul (at x 'j) (b/column-left A y m 'j)))
        C (lp/products 'c x) B (lp/products 'b y)
        row-eq (a/sum-cong L B m 'i
                 (fn [i hi]
                   (let [rx (lp/row A x n i) bi (at 'b i) yi (at y i)]
                     (a/chain (mul yi (row-left i))
                       [(mul yi rx)
                        (a/mul-cong yi yi (row-left i) rx (refl yi)
                          (a/sum-cong (f/lam [['j nat]] (mul (at x 'j) (at A i 'j)))
                            (f/lam [['j nat]] (mul (at A i 'j) (at x 'j))) n 'j
                            (fn [j _] (call 'signed/multiply-commutative (at x j) (at A i j)))))]
                       [(mul yi bi) (a/mul-cong yi yi rx bi (refl yi) (at 'rows i hi))]
                       [(mul bi yi) (call 'signed/multiply-commutative yi bi)]))))
        bound (a/sum-mono R C n 'j
                (fn [j hj]
                  (let [xj (at x j) cj (at 'c j) old (b/column-left A y m j) col (lp/column A y m j)
                        hd (s/le-transport col old cj cj
                             (sym old col (call 'signed/expr-sum-column-commute A y m j)) (refl cj) (at 'dual j hj))]
                    (s/le-transport (mul xj old) (mul xj old) (mul xj cj) (mul cj xj)
                      (refl (mul xj old)) (call 'signed/multiply-commutative xj cj)
                      (call 'signed/multiply-left-monotone xj old cj (at 'xn j hj) hd)))))
        swap (call 'signed/bilinear-swap y x A m n)]
    (s/spec 'signed/expr-sum-equality-lp-weak-duality
      [['A lp/matrix] ['b family] ['c family] ['x family] ['y family] ['m nat] ['n nat]
       ['rows (equality-feasible A 'b x m n)] ['xn (lp/nonnegative x n)]
       ['dual (b/covering-dual A 'c y m n)]]
      (le (sum B m) (sum C n))
      (s/le-transport (sum R n) (sum B m) (sum C n) (sum C n)
        (s/trans (sum R n) (sum L m) (sum B m) (sym (sum L m) (sum R n) swap) row-eq)
        (refl (sum C n)) bound))))

(def borrowed-specs [dea/bilinear-swap-spec])
(def theorem-specs [weak-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.multiply-associative
            rainbow.math.linear.matrix.action-scale])
(defn install [env]
  (-> env (support/extend-with-shared :expr-sum-equality-lp-bound borrowed-specs)
      (support/extend-with :expr-sum-equality-lp-bound theorem-specs)))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.equality-lp-bound))
