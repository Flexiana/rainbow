(ns rainbow.math.sums.binary-capacity
  "For binary entries, x+y<=1 means selecting x excludes y."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.sums.value-algebra :as s :refer [signed call at le eqv refl]]
            [rainbow.math.sums.lp-bounds :as b] [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.boolean-predicate :as bits]
            [rainbow.math.milestone-support :as support] [rainbow.module :as module]))
(defn excess [x y] (a/sub (s/add x y) b/one))
(def upper-spec
  (s/spec 'signed/boolean-cases-at-most-one [['x signed] ['binary (bits/binary 'x)]] (le 'x b/one)
    (a/cases (eqv 'x s/zero) (eqv 'x b/one) (le 'x b/one) 'binary
      (f/lam [['zero (eqv 'x s/zero)]]
        (s/le-transport s/zero 'x b/one b/one (s/sym 'x s/zero 'zero) (refl b/one)
          (call 'signed/less-than-implies-at-most s/zero b/one (f/const* 'signed/zero-less-than-one []))))
      (f/lam [['one (eqv 'x b/one)]] (a/eq-le 'x b/one 'one)))))
(def forward-spec
  (let [x 'x y 'y xy (excess x y)
        reduces (s/trans xy (excess b/one y) y
                  (s/add-cong (s/add x y) (s/add b/one y) (a/neg b/one) (a/neg b/one)
                    (s/add-cong x b/one y y 'selected (refl y)) (refl (a/neg b/one)))
                  (a/ring-eq (excess b/one y) y))]
    (s/spec 'signed/binary-capacity-implies-exclusion
      [[x signed] [y signed] ['yb (bits/binary y)] ['capacity (le xy s/zero)] ['selected (eqv x b/one)]]
      (eqv y s/zero)
      (call 'signed/at-most-antisymmetric y s/zero
        (s/le-transport xy y s/zero s/zero reduces (refl s/zero) 'capacity)
        (call 'signed/boolean-cases-nonnegative y 'yb)))))
(def backward-spec
  (let [x 'x y 'y xy (excess x y)
        ex (f/arrow (eqv x b/one) (eqv y s/zero))
        swap (fn [X Y hx hy]
               (s/add-cong (s/add x y) (s/add X Y) (a/neg b/one) (a/neg b/one)
                 (s/add-cong x X y Y hx hy) (refl (a/neg b/one))))]
    (s/spec 'signed/binary-exclusion-implies-capacity
      [[x signed] [y signed] ['xb (bits/binary x)] ['yb (bits/binary y)] ['exclusion ex]] (le xy s/zero)
      (a/cases (eqv x s/zero) (eqv x b/one) (le xy s/zero) 'xb
        (f/lam [['zero (eqv x s/zero)]]
          (s/le-transport (a/sub y b/one) xy s/zero s/zero
            (s/sym xy (a/sub y b/one)
              (s/trans xy (excess s/zero y) (a/sub y b/one) (swap s/zero y 'zero (refl y))
                (a/ring-eq (excess s/zero y) (a/sub y b/one)))) (refl s/zero)
            (call 'signed/at-most-implies-nonpositive-difference y b/one (call 'signed/boolean-cases-at-most-one y 'yb))))
        (f/lam [['one (eqv x b/one)]]
          (a/eq-le xy s/zero
            (s/trans xy (excess b/one s/zero) s/zero (swap b/one s/zero 'one (at 'exclusion 'one))
              (a/ring-eq (excess b/one s/zero) s/zero))))))))
(def theorem-specs [upper-spec forward-spec backward-spec])
(def deps '[rainbow.math.sums.zero-violations])
(defn install [env] (support/extend-with env :expr-sum-binary-capacity theorem-specs))
(defn extend-environment [env] (module/install-module env 'rainbow.math.sums.binary-capacity))
