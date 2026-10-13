(ns rainbow.math.sums.triangular
  "Triangular decomposition for the existing finite sums; prefix completion costs.
  Pure algebra, with no schedule or permutation assumptions."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add mul eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a]))
(def matrix (f/arrow nat family))
(defn row [M i] (f/lam [['tr-col nat]] (at M i 'tr-col)))
(defn column [M j] (f/lam [['tr-row nat]] (at M 'tr-row j)))
(defn square [M n] (sum (f/lam [['tr-outer nat]] (sum (row M 'tr-outer) n)) n))
(defn triangle [M n]
  (sum (f/lam [['tr-later nat]] (sum (column M 'tr-later) 'tr-later)) n))
(defn transpose [M] (f/lam [['tr-a nat] ['tr-b nat]] (at M 'tr-b 'tr-a)))
(defn diagonal [M n] (sum (f/lam [['tr-diag nat]] (at M 'tr-diag 'tr-diag)) n))
(defn products [P W] (f/lam [['tr-p nat] ['tr-w nat]] (mul (at P 'tr-p) (at W 'tr-w))))
(defn completion-cost [P W n]
  (sum (f/lam [['tr-position nat]] (mul (at W 'tr-position) (sum P (s/succ 'tr-position)))) n))
(def square-step-spec
  (let [M 'tr-matrix n 'tr-size
        oldrows (f/lam [['tr-i nat]] (sum (row M 'tr-i) n))
        newrows (f/lam [['tr-i nat]] (sum (row M 'tr-i) (s/succ n)))
        col (column M n)
        joined (f/lam [['tr-i nat]] (add (at oldrows 'tr-i) (at col 'tr-i)))
        goal (add (add (square M n) (sum (row M n) n)) (add (sum col n) (at M n n)))]
    (s/spec 'signed/expr-sum-square-successor [[M matrix] [n nat]]
      (eqv (square M (s/succ n)) goal)
      (s/trans (square M (s/succ n)) (sum joined (s/succ n)) goal
        (a/sum-cong newrows joined (s/succ n) 'tr-expand
          (fn [i _] (refl (sum (row M i) (s/succ n)))))
        (call 'signed/expr-sum-value-add oldrows col (s/succ n))))))
(def decomposition-spec
  (let [M 'tr-matrix MT (transpose M)
        rhs (fn [n] (add (add (triangle M n) (triangle MT n)) (diagonal M n)))
        claim (fn [n] (eqv (square M n) (rhs n)))]
    (s/spec 'signed/expr-sum-square-triangular-decomposition [[M matrix] ['tr-size nat]]
      (claim 'tr-size)
      (s/induct claim (a/ring-eq s/zero (add (add s/zero s/zero) s/zero))
        (fn [n ih]
          (let [sq (square M n) lower (triangle M n) upper (triangle MT n) diag (diagonal M n)
                r (sum (row M n) n) c (sum (column M n) n) d (at M n n)
                expanded (add (add sq r) (add c d))
                replaced (add (add (rhs n) r) (add c d))
                target (add (add (add lower c) (add upper r)) (add diag d))]
            (a/chain (square M (s/succ n))
              [expanded (call 'signed/expr-sum-square-successor M n)]
              [replaced (s/add-cong (add sq r) (add (rhs n) r) (add c d) (add c d)
                          (s/add-cong sq (rhs n) r r ih (refl r)) (refl (add c d)))]
              [target (a/ring-eq replaced target)]))) 'tr-size))))
(defn symmetric [M n]
  (f/forall [['tr-i nat] ['tr-ib (s/below 'tr-i n)] ['tr-j nat] ['tr-jb (s/below 'tr-j n)]]
    (eqv (at M 'tr-i 'tr-j) (at M 'tr-j 'tr-i))))
(def symmetric-spec
  (let [M 'tr-matrix n 'tr-size MT (transpose M) tri (triangle M n) upper (triangle MT n)
        diag (diagonal M n)
        transposed (a/sum-cong
                     (f/lam [['tr-later nat]] (sum (column MT 'tr-later) 'tr-later))
                     (f/lam [['tr-later nat]] (sum (column M 'tr-later) 'tr-later)) n 'tr-k
                     (fn [k hk]
                       (a/sum-cong (column MT k) (column M k) k 'tr-h
                         (fn [h hh]
                           (at 'tr-symmetric k hk h
                             (call 'nat/at-most-transitive (s/succ h) k n hh
                               (call 'nat/at-most-transitive k (s/succ k) n (call 'nat/at-most-successor k) hk)))))))]
    (s/spec 'signed/expr-sum-symmetric-triangular [[M matrix] [n nat] ['tr-symmetric (symmetric M n)]]
      (eqv (square M n) (add (add tri tri) diag))
      (s/trans (square M n) (add (add tri upper) diag) (add (add tri tri) diag)
        (call 'signed/expr-sum-square-triangular-decomposition M n)
        (s/add-cong (add tri upper) (add tri tri) diag diag
          (s/add-cong tri tri upper tri (refl tri) transposed) (refl diag))))))
(def prefix-cost-spec
  (let [P 'tr-times W 'tr-weights n 'tr-size M (products P W)
        cols (f/lam [['tr-k nat]] (sum (column M 'tr-k) 'tr-k))
        diags (f/lam [['tr-k nat]] (mul (at P 'tr-k) (at W 'tr-k)))
        joined (f/lam [['tr-k nat]] (add (at cols 'tr-k) (at diags 'tr-k)))
        costs (f/lam [['tr-k nat]] (mul (at W 'tr-k) (sum P (s/succ 'tr-k))))]
    (s/spec 'signed/expr-sum-prefix-completion-cost [[P family] [W family] [n nat]]
      (eqv (completion-cost P W n) (add (triangle M n) (diagonal M n)))
      (s/trans (completion-cost P W n) (sum joined n) (add (triangle M n) (diagonal M n))
        (a/sum-cong costs joined n 'tr-at
          (fn [k _]
            (let [pk (at P k) wk (at W k) prefix (sum P k)
                  small (add (mul prefix wk) (mul pk wk))
                  result (add (sum (column M k) k) (mul pk wk))]
              (s/trans (mul wk (sum P (s/succ k))) small result
                (a/ring-eq (mul wk (add prefix pk)) small)
                (s/add-cong (mul prefix wk) (sum (column M k) k) (mul pk wk) (mul pk wk)
                  (call 'signed/expr-sum-value-scale-right P wk k) (refl (mul pk wk)))))))
        (call 'signed/expr-sum-value-add cols diags n)))))
(def theorem-specs [square-step-spec decomposition-spec symmetric-spec prefix-cost-spec])
(defn extend-environment [env]
  (reduce (fn [checked spec]
            (println :triangular :installing (:name spec)) (flush)
            (support/add-spec-shared checked :expr-sum-triangular spec))
          (a/extend-environment env) theorem-specs))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
