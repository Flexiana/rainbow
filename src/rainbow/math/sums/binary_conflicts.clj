(ns rainbow.math.sums.binary-conflicts
  "Reusable bridges from binary entries and nonpositive nonnegative sums to exclusions."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.boolean-predicate :as bits]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(def nonnegative-spec
  (let [x 'x P (eqv x s/zero) Q (eqv x b/one)
        branch (fn [v h]
                 (f/lam [['value (eqv x v)]]
                   (s/le-transport s/zero s/zero v x (refl s/zero) (s/sym x v 'value) h)))]
    (s/spec 'signed/boolean-cases-nonnegative [[x signed] ['binary (bits/binary x)]] (le s/zero x)
      (a/cases P Q (le s/zero x) 'binary
        (branch s/zero (call 'signed/at-most-reflexive s/zero))
        (branch b/one (call 'signed/less-than-implies-at-most s/zero b/one (f/const* 'signed/zero-less-than-one [])))))))
(defn nnprod [x y hx hy]
  (s/le-transport (mul x s/zero) s/zero (mul x y) (mul x y)
    (call 'signed/multiply-zero-right x) (refl (mul x y))
    (call 'signed/multiply-left-monotone x s/zero y hx hy)))
(def term-zero-spec
  (s/spec 'signed/nonnegative-nonpositive-sum-term-zero
    [['F family] ['n nat] ['nonnegative (s/all-below 'n #(le s/zero (at 'F %)))]
     ['nonpositive (le (sum 'F 'n) s/zero)] ['i nat] ['bound (s/below 'i 'n)]]
    (eqv (at 'F 'i) s/zero)
    (call 'signed/expr-sum-value-nonnegative-terms-zero 'F 'n 'nonnegative
      (call 'signed/at-most-antisymmetric (sum 'F 'n) s/zero 'nonpositive
        (call 'signed/expr-sum-value-nonnegative 'F 'n 'nonnegative)) 'i 'bound)))
(def exclusion-spec
  (let [x 'x y 'y z 'z goal (eqv (mul x (mul y z)) s/zero)
        excluded (f/arrow (eqv x b/one) (eqv y b/one) (eqv z s/zero))
        xzero (s/trans (mul x (mul y z)) (mul s/zero (mul y z)) s/zero
                (a/mul-cong x s/zero (mul y z) (mul y z) 'xzero (refl (mul y z)))
                (call 'signed/multiply-zero-left (mul y z)))
        yzero (a/chain (mul x (mul y z))
                [(mul x (mul s/zero z)) (a/mul-cong x x (mul y z) (mul s/zero z) (refl x)
                                        (a/mul-cong y s/zero z z 'yzero (refl z)))]
                [(mul x s/zero) (a/mul-cong x x (mul s/zero z) s/zero (refl x) (call 'signed/multiply-zero-left z))]
                [s/zero (call 'signed/multiply-zero-right x)])
        zzero (a/chain (mul x (mul y z))
                [(mul x (mul y s/zero)) (a/mul-cong x x (mul y z) (mul y s/zero) (refl x)
                                         (a/mul-cong y y z s/zero (refl y) (at 'excluded 'xone 'yone)))]
                [(mul x s/zero) (a/mul-cong x x (mul y s/zero) s/zero (refl x) (call 'signed/multiply-zero-right y))]
                [s/zero (call 'signed/multiply-zero-right x)])]
    (s/spec 'signed/binary-exclusion-zero-product
      [[x signed] [y signed] [z signed] ['xb (bits/binary x)] ['yb (bits/binary y)] ['excluded excluded]] goal
      (a/cases (eqv x s/zero) (eqv x b/one) goal 'xb
        (f/lam [['xzero (eqv x s/zero)]] xzero)
        (f/lam [['xone (eqv x b/one)]]
          (a/cases (eqv y s/zero) (eqv y b/one) goal 'yb
            (f/lam [['yzero (eqv y s/zero)]] yzero)
            (f/lam [['yone (eqv y b/one)]] zzero)))))))
(def theorem-specs [nonnegative-spec term-zero-spec exclusion-spec])
(def deps '[rainbow.math.sums.boolean-predicate rainbow.math.sums.nonneg-zero
            rainbow.math.rational.signed.strict-order])
(defn install [env] (support/extend-with env :expr-sum-binary-conflicts theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.binary-conflicts))
