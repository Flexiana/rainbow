(ns rainbow.math.lemmas.lsq-optimal
  "General lemmas: lsq optimal. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add mul eqv le refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.game-value :as game]
            [rainbow.math.sums.nonneg-zero :as nn]
            [rainbow.math.rational.signed.square-of-sum :as sos]
            [rainbow.math.linear.vector.norm-nonnegative :as norm]))

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(def two (add one one))

(defn sub [x y] (a/sub x y))

(defn sq [x] (mul x x))

(defn difference [z x] (f/lam [['dj nat]] (sub (at z 'dj) (at x 'dj))))

(defn action [A x n] (f/lam [['ai nat]] (game/row A x n 'ai)))

(defn residual [A b x n] (f/lam [['ri nat]] (sub (game/row A x n 'ri) (at b 'ri))))

(defn normal [A r m] (f/lam [['nj nat]] (sum (f/lam [['ni nat]] (mul (at A 'ni 'nj) (at r 'ni))) m)))

(defn norm2 [x n] (sum (f/lam [['sq-i nat]] (sq (at x 'sq-i))) n))

(defn dot [x y n] (sum (f/lam [['dot-i nat]] (mul (at x 'dot-i) (at y 'dot-i))) n))

(defn all-at [i n t] (f/forall [[i nat] [(symbol (str i "-lt")) (below i n)]] t))

(defn each [i n body]
  (let [h (symbol (str i "-lt"))] (f/lam [[i nat] [h (below i n)]] (body i h))))

(defn mc [x y z w h k] (a/mul-cong x y z w h k))

(defn ac [x y z w h k] (s/add-cong x y z w h k))

(defn sc [F G n i h] (a/sum-cong F G n i h))

(defn residual-agrees [A b x r m n]
  (all-at 'ri m (eqv (at r 'ri) (at (residual A b x n) 'ri))))

(defn normal-zero [A r m n]
  (all-at 'nj n (eqv (at (normal A r m) 'nj) s/zero)))

(defn expanded [A x r z m n]
  (let [d (difference z x)]
    (add (add (norm2 r m) (norm2 (action A d n) m))
         (mul two (dot d (normal A r m) n)))))

(def row-difference-spec
  (let [d (difference 'z 'x)
        F (f/lam [['j nat]] (mul (at 'A 'i 'j) (at 'z 'j)))
        G (f/lam [['j nat]] (mul (at 'A 'i 'j) (at 'x 'j)))
        H (f/lam [['j nat]] (mul (at 'A 'i 'j) (at d 'j)))
        D (f/lam [['j nat]] (sub (at F 'j) (at G 'j)))
        lhs (game/row 'A d 'n 'i) rhs (sub (game/row 'A 'z 'n 'i) (game/row 'A 'x 'n 'i))]
    (s/spec 'signed/lsq-row-difference
            [['A matrix] ['z family] ['x family] ['n nat] ['i nat]] (eqv lhs rhs)
            (trans lhs (sum D 'n) rhs
                   (sc H D 'n 'j (fn [j _] (a/ring-eq (mul (at 'A 'i j) (sub (at 'z j) (at 'x j))) (sub (mul (at 'A 'i j) (at 'z j)) (mul (at 'A 'i j) (at 'x j))))))
                   (call 'signed/expr-sum-value-subtract F G 'n)))))

(def residual-change-spec
  (let [d (difference 'z 'x) u (game/row 'A 'z 'n 'i) v (game/row 'A 'x 'n 'i)
        r (at 'r 'i) b (at 'b 'i) w (game/row 'A d 'n 'i)
        lhs (sub u b) rhs (add r w) mid (add (sub v b) (sub u v))]
    (s/spec 'signed/lsq-residual-change
            [['A matrix] ['b family] ['x family] ['r family] ['z family] ['n nat] ['i nat]
             ['hr (eqv r (sub v b))]]
            (eqv lhs rhs)
            (trans lhs mid rhs (a/ring-eq lhs mid)
                   (ac (sub v b) r (sub u v) w (sym r (sub v b) 'hr)
                       (sym w (sub u v) (call 'signed/lsq-row-difference 'A 'z 'x 'n 'i)))))))

(def square-expansion-spec
  (let [x 'x y 'y lhs (sq (add x y))
        middle (add (add (sq x) (mul x y)) (add (mul y x) (sq y)))
        base (add (sq x) (sq y)) xy (mul x y)
        collected (add base (add xy xy)) rhs (add base (mul two xy))
        twice (trans (mul two xy) (add (mul one xy) (mul one xy)) (add xy xy)
                     (call 'signed/multiply-distributes-add-right one one xy)
                     (ac (mul one xy) xy (mul one xy) xy
                         (call 'signed/multiply-one-left xy) (call 'signed/multiply-one-left xy)))]
    (s/spec 'signed/lsq-square-expansion [['x signed] ['y signed]] (eqv lhs rhs)
            (a/chain lhs [middle (call 'signed/square-of-sum x y)]
                     [collected (a/ring-eq middle collected)]
                     [rhs (ac base base (add xy xy) (mul two xy) (refl base)
                              (sym (mul two xy) (add xy xy) twice))]))))

(def norm-add-spec
  (let [R (f/lam [['i nat]] (sq (at 'r 'i))) D (f/lam [['i nat]] (sq (at 'd 'i)))
        C (f/lam [['i nat]] (mul (at 'r 'i) (at 'd 'i)))
        RD (f/lam [['i nat]] (add (at R 'i) (at D 'i)))
        TC (f/lam [['i nat]] (mul two (at C 'i)))
        H (f/lam [['i nat]] (sq (add (at 'r 'i) (at 'd 'i))))
        E (f/lam [['i nat]] (add (at RD 'i) (at TC 'i)))
        lhs (sum H 'm) rhs (add (add (norm2 'r 'm) (norm2 'd 'm)) (mul two (dot 'r 'd 'm)))]
    (s/spec 'signed/expr-sum-norm-add-expansion [['r family] ['d family] ['m nat]] (eqv lhs rhs)
            (a/chain lhs
                     [(sum E 'm) (sc H E 'm 'i (fn [i _] (call 'signed/lsq-square-expansion (at 'r i) (at 'd i))))]
                     [(add (sum RD 'm) (sum TC 'm)) (call 'signed/expr-sum-value-add RD TC 'm)]
                     [rhs (ac (sum RD 'm) (add (sum R 'm) (sum D 'm))
                              (sum TC 'm) (mul two (sum C 'm))
                              (call 'signed/expr-sum-value-add R D 'm)
                              (sym (mul two (sum C 'm)) (sum TC 'm)
                                   (call 'signed/expr-sum-value-scale-left C two 'm)))]))))

(def cross-spec
  (let [lhs (dot 'r (action 'A 'd 'n) 'm)
        cf (#'game/column-form 'A 'r 'd 'm 'n)
        rhs (dot 'd (normal 'A 'r 'm) 'n)
        F (f/lam [['j nat]] (mul (game/column 'A 'r 'm 'j) (at 'd 'j)))
        G (f/lam [['j nat]] (mul (at 'd 'j) (at (normal 'A 'r 'm) 'j)))]
    (s/spec 'signed/lsq-cross-normal [['A matrix] ['r family] ['d family] ['m nat] ['n nat]] (eqv lhs rhs)
            (trans lhs cf rhs (call 'signed/game-payoff-column-form 'A 'r 'd 'm 'n)
                   (sc F G 'n 'j
                       (fn [j _]
                         (let [c (game/column 'A 'r 'm j) nr (at (normal 'A 'r 'm) j) d (at 'd j)
                               h (sc (f/lam [['i nat]] (mul (at 'r 'i) (at 'A 'i j)))
                                     (f/lam [['i nat]] (mul (at 'A 'i j) (at 'r 'i))) 'm 'i
                                     (fn [i _] (call 'signed/multiply-commutative (at 'r i) (at 'A i j))))]
                           (trans (mul c d) (mul d c) (mul d nr)
                                  (call 'signed/multiply-commutative c d)
                                  (mc d d c nr (refl d) h)))))))))

(def decomposition-spec
  (let [d (difference 'z 'x) ad (action 'A d 'n) rz (residual 'A 'b 'z 'n)
        H (f/lam [['i nat]] (sq (at rz 'i)))
        G (f/lam [['i nat]] (sq (add (at 'r 'i) (at ad 'i))))
        lhs (norm2 rz 'm) base (add (norm2 'r 'm) (norm2 ad 'm))
        mid (add base (mul two (dot 'r ad 'm))) rhs (expanded 'A 'x 'r 'z 'm 'n)]
    (s/spec 'signed/expr-sum-lsq-decomposition
            [['A matrix] ['b family] ['x family] ['r family] ['z family] ['m nat] ['n nat]
             ['hr (residual-agrees 'A 'b 'x 'r 'm 'n)]]
            (eqv lhs rhs)
            (a/chain lhs
                     [(sum G 'm) (sc H G 'm 'i (fn [i hi]
                       (let [v (at rz i) w (add (at 'r i) (at ad i))
                             h (call 'signed/lsq-residual-change 'A 'b 'x 'r 'z 'n i (at 'hr i hi))]
                         (mc v w v w h h))))]
                     [mid (call 'signed/expr-sum-norm-add-expansion 'r ad 'm)]
                     [rhs (ac base base (mul two (dot 'r ad 'm)) (mul two (dot d (normal 'A 'r 'm) 'n))
                              (refl base) (mc two two (dot 'r ad 'm) (dot d (normal 'A 'r 'm) 'n)
                                              (refl two) (call 'signed/lsq-cross-normal 'A 'r d 'm 'n)))]))))

(def normal-dot-zero-spec
  (let [N (normal 'A 'r 'm) F (f/lam [['j nat]] (mul (at 'd 'j) (at N 'j))) Z (f/lam [['j nat]] s/zero)]
    (s/spec 'signed/lsq-normal-dot-zero
            [['A matrix] ['r family] ['d family] ['m nat] ['n nat] ['hn (normal-zero 'A 'r 'm 'n)]]
            (eqv (dot 'd N 'n) s/zero)
            (trans (dot 'd N 'n) (sum Z 'n) s/zero
                   (sc F Z 'n 'j (fn [j hj]
                     (let [d (at 'd j) v (at N j)]
                       (trans (mul d v) (mul d s/zero) s/zero
                              (mc d d v s/zero (refl d) (at 'hn j hj))
                              (call 'signed/multiply-zero-right d)))))
                   (call 'signed/expr-sum-value-zero 'n)))))

(def optimal-spec
  (let [d (difference 'z 'x) ad (action 'A d 'n)
        rr (norm2 'r 'm) dd (norm2 ad 'm) target (norm2 (residual 'A 'b 'z 'n) 'm)
        cr (dot d (normal 'A 'r 'm) 'n) base (add rr dd)
        exp (expanded 'A 'x 'r 'z 'm 'n)
        cross0 (trans (mul two cr) (mul two s/zero) s/zero
                      (mc two two cr s/zero (refl two) (call 'signed/lsq-normal-dot-zero 'A 'r d 'm 'n 'hn))
                      (call 'signed/multiply-zero-right two))
        exp-base (trans exp (add base s/zero) base
                        (ac base base (mul two cr) s/zero (refl base) cross0)
                        (call 'signed/add-zero-right base))
        target-base (trans target exp base (call 'signed/expr-sum-lsq-decomposition 'A 'b 'x 'r 'z 'm 'n 'hr) exp-base)
        dd0 (call 'signed/expr-sum-value-nonnegative (f/lam [['i nat]] (sq (at ad 'i))) 'm
                  (each 'i 'm (fn [i _]
                    (call 'signed/zero-at-most-of-nonnegative (sq (at ad i)) (call 'signed/square-nonnegative (at ad i))))))]
    (s/spec 'signed/expr-sum-lsq-optimal
            [['A matrix] ['b family] ['x family] ['r family] ['z family] ['m nat] ['n nat]
             ['hr (residual-agrees 'A 'b 'x 'r 'm 'n)] ['hn (normal-zero 'A 'r 'm 'n)]]
            (le rr target)
            (s/le-transport (add rr s/zero) rr base target (call 'signed/add-zero-right rr)
                            (sym target base target-base)
                            (call 'signed/add-monotone rr rr s/zero dd (call 'signed/at-most-reflexive rr) dd0)))))

(defn conjunction [xs] (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [row-difference-spec residual-change-spec square-expansion-spec norm-add-spec cross-spec decomposition-spec normal-dot-zero-spec optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      game/extend-environment
      nn/extend-environment
      sos/extend-environment
      norm/extend-environment
      (support/extend-with :expr-sum-lsq-optimal theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
