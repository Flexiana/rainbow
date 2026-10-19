(ns rainbow.math.sums.budgeted-protection
  "Weak duality for a budgeted box: 0<=w<=1, sum w<=Gamma and
  d_j<=z+p_j, z,p>=0 imply sum w_j*d_j<=Gamma*z+sum p_j."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul add le eqv refl sym]]
            [rainbow.math.lemmas.lp-duality :as lp]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.milestone-support :as support]
            [rainbow.module :as module]))

(defn protection [gamma z p n] (add (mul gamma z) (sum p n)))
(def split-spec
  (let [covered (f/lam [['j nat]] (mul (at 'w 'j) (add 'z (at 'p 'j))))
        wz (f/lam [['j nat]] (mul (at 'w 'j) 'z)) wp (lp/products 'w 'p)
        added (f/lam [['j nat]] (add (at wz 'j) (at wp 'j)))
        result (add (mul (sum 'w 'n) 'z) (sum wp 'n))]
    (s/spec 'signed/budgeted-protection-split [['w family] ['p family] ['z signed] ['n nat]]
      (eqv (sum covered 'n) result)
      (a/chain (sum covered 'n)
        [(sum added 'n) (a/sum-cong covered added 'n 'j
                         (fn [j _] (call 'signed/multiply-distributes-add-left (at 'w j) 'z (at 'p j))))]
        [(add (sum wz 'n) (sum wp 'n)) (call 'signed/expr-sum-value-add wz wp 'n)]
        [result (s/add-cong (sum wz 'n) (mul (sum 'w 'n) 'z) (sum wp 'n) (sum wp 'n)
                  (sym (mul (sum 'w 'n) 'z) (sum wz 'n) (call 'signed/expr-sum-value-scale-right 'w 'z 'n))
                  (refl (sum wp 'n)))]))))

(def bound-spec
  (let [covered (f/lam [['j nat]] (mul (at 'w 'j) (add 'z (at 'p 'j))))
        wp (lp/products 'w 'p) wd (lp/products 'w 'd)
        lhs (sum wd 'n) middle (add (mul (sum 'w 'n) 'z) (sum wp 'n))
        rhs (protection 'gamma 'z 'p 'n)
        first-bound (a/sum-mono wd covered 'n 'j
                      (fn [j hj] (call 'signed/multiply-left-monotone (at 'w j) (at 'd j) (add 'z (at 'p j))
                                   (at 'wn j hj) (at 'cover j hj))))
        p-bound (a/sum-mono wp 'p 'n 'j
                  (fn [j hj]
                    (s/le-transport (mul (at 'w j) (at 'p j)) (mul (at 'w j) (at 'p j))
                      (mul b/one (at 'p j)) (at 'p j) (refl (mul (at 'w j) (at 'p j)))
                      (call 'signed/multiply-one-left (at 'p j))
                      (call 'signed/multiply-right-monotone (at 'p j) (at 'w j) b/one
                        (at 'pn j hj) (at 'wu j hj)))))
        last-bound (call 'signed/add-monotone (mul (sum 'w 'n) 'z) (mul 'gamma 'z) (sum wp 'n) (sum 'p 'n)
                     (call 'signed/multiply-right-monotone 'z (sum 'w 'n) 'gamma 'zn 'budget) p-bound)]
    (s/spec 'signed/budgeted-protection-bound
      [['w family] ['d family] ['p family] ['z signed] ['gamma signed] ['n nat]
       ['wn (lp/nonnegative 'w 'n)] ['wu (s/all-below 'n #(le (at 'w %) b/one))]
       ['budget (le (sum 'w 'n) 'gamma)] ['zn (le s/zero 'z)] ['pn (lp/nonnegative 'p 'n)]
       ['cover (s/all-below 'n #(le (at 'd %) (add 'z (at 'p %))))]]
      (le lhs rhs)
      (call 'signed/at-most-transitive lhs middle rhs
        (s/le-transport lhs lhs (sum covered 'n) middle (refl lhs)
          (call 'signed/budgeted-protection-split 'w 'p 'z 'n) first-bound) last-bound))))

(def theorem-specs [split-spec bound-spec])
(def deps '[rainbow.math.sums.lp-bounds rainbow.math.rational.signed.order-monotone
            rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.distributive])
(defn install [env] (support/extend-with env :expr-sum-budgeted-protection theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.budgeted-protection))
