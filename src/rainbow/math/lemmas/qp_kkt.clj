(ns rainbow.math.lemmas.qp-kkt
  "General lemmas: qp kkt. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add mul eqv le refl sym trans below]]
            [rainbow.math.lemmas.game-value :as game]
            [rainbow.math.lemmas.bb-leaf-bound :as bb]
            [rainbow.math.sums.flow-cut :as ring]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]
            [rainbow.math.rational.signed.order-cancellation :as order-cancel]))

(def matrix (f/arrow nat family))

(def half (call 'signed/from-nnrat (f/const* 'nnrat/half [])))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn scale [x] (mul half x))

(defn dot [x y n] (sum (f/lam [['d nat]] (mul (at x 'd) (at y 'd))) n))

(defn action [A x n] (f/lam [['r nat]] (game/row A x n 'r)))

(defn quad [Q x n] (game/payoff Q x x n n))

(defn objective [Q c x n] (add (scale (quad Q x n)) (dot c x n)))

(defn all-at [i n body] (f/forall [[i nat] [(symbol (str i "-lt")) (below i n)]] body))

(defn each [i n body]
  (let [h (symbol (str i "-lt"))] (f/lam [[i nat] [h (below i n)]] (body i h))))

(defn sum-cong [F G n h] (call 'signed/expr-sum-value-respects-equivalence-below F G n h))

(defn mc [a b c d h k] (call 'signed/multiply-respects-equivalence a b c d h k))

(defn ac [a b c d h k] (s/add-cong a b c d h k))

(defn lr [a b c d h k p] (s/le-transport a b c d h k p))

(defn gram-entry [R n i j]
  (sum (f/lam [['g nat]] (mul (at R 'g i) (at R 'g j))) n))

(defn gram [Q R n]
  (all-at 'gi n (all-at 'gj n (eqv (at Q 'gi 'gj) (gram-entry R n 'gi 'gj)))))

(defn sc [F c n] (call 'signed/expr-sum-value-scale-left F c n))

(defn sum-add [F G n] (call 'signed/expr-sum-value-add F G n))

(defn scaled-plus-sum [F G n]
  (let [H (f/lam [['sp nat]] (add (scale (at F 'sp)) (at G 'sp)))
        HF (f/lam [['sp nat]] (scale (at F 'sp)))
        a (sum H n) b (add (sum HF n) (sum G n)) c (add (scale (sum F n)) (sum G n))]
    (trans a b c (sum-add HF G n)
           (ac (sum HF n) (scale (sum F n)) (sum G n) (sum G n)
               (sym (scale (sum F n)) (sum HF n) (sc F half n)) (refl (sum G n))))))

(def gram-action-spec
  (let [rx (action 'R 'x 'n) rc (f/lam [['k nat]] (at 'R 'k 'column-index))
        row (game/row 'Q 'x 'n 'column-index)
        gf (f/lam [['l nat]] (mul (gram-entry 'R 'n 'column-index 'l) (at 'x 'l)))
        cf (#'game/column-form 'R rc 'x 'n 'n)
        p (game/payoff 'R rc 'x 'n 'n)
        col (game/column 'R rx 'n 'column-index)
        qf (f/lam [['l nat]] (mul (at 'Q 'column-index 'l) (at 'x 'l)))]
    (s/spec 'signed/qp-gram-action
            [['Q matrix] ['R matrix] ['x family] ['n nat] ['gram (gram 'Q 'R 'n)]
             ['column-index nat] ['column-indexb (below 'column-index 'n)]]
            (eqv row col)
            (trans row cf col
                   (sum-cong qf gf 'n (each 'l 'n (fn [l hl]
                     (mc (at 'Q 'column-index l) (gram-entry 'R 'n 'column-index l) (at 'x l) (at 'x l)
                         (at 'gram 'column-index 'column-indexb l hl) (refl (at 'x l))))))
                   (trans cf p col
                          (sym p cf (call 'signed/game-payoff-column-form 'R rc 'x 'n 'n))
                          (sum-cong (f/lam [['k nat]] (mul (at 'R 'k 'column-index) (at rx 'k)))
                                    (f/lam [['k nat]] (mul (at rx 'k) (at 'R 'k 'column-index))) 'n
                                    (each 'k 'n (fn [k _] (call 'signed/multiply-commutative (at 'R k 'column-index) (at rx k))))))))))

(def gram-bilinear-spec
  (let [rx (action 'R 'x 'n) rz (action 'R 'z 'n)
        p (game/payoff 'Q 'z 'x 'n 'n)
        F (f/lam [['bi nat]] (mul (at 'z 'bi) (game/row 'Q 'x 'n 'bi)))
        G (f/lam [['bi nat]] (mul (game/column 'R rx 'n 'bi) (at 'z 'bi)))
        cf (#'game/column-form 'R rx 'z 'n 'n)
        result (dot rx rz 'n)]
    (s/spec 'signed/qp-gram-bilinear
            [['Q matrix] ['R matrix] ['x family] ['z family] ['n nat] ['gram (gram 'Q 'R 'n)]]
            (eqv p result)
            (trans p cf result
                   (sum-cong F G 'n (each 'bi 'n (fn [j hj]
                     (let [v (game/row 'Q 'x 'n j) w (game/column 'R rx 'n j) z (at 'z j)]
                       (trans (mul z v) (mul z w) (mul w z)
                              (mc z z v w (refl z) (call 'signed/qp-gram-action 'Q 'R 'x 'n 'gram j hj))
                              (call 'signed/multiply-commutative z w))))))
                   (sym result cf (call 'signed/game-payoff-column-form 'R rx 'z 'n 'n))))))

(defn collect-scale [tree]
  (let [[tag head l r] (when (vector? tree) tree)]
    (if (and (= tag :app) (= head (f/const* 'signed/add [])))
      (let [[ls lh] (collect-scale l) [rs rh] (collect-scale r)
            out (add ls rs) mid (add (scale l) (scale r))]
        [out (trans out mid (scale tree) (ac ls (scale l) rs (scale r) lh rh)
                    (sym (scale tree) mid (call 'signed/multiply-distributes-add-left half l r)))])
      [(scale tree) (refl (scale tree))])))

(def square-difference-spec
  (let [aa (mul 'a 'a) ab (mul 'a 'b) bb (mul 'b 'b)
        dd (mul (sub 'a 'b) (sub 'a 'b))
        lhs (add (add aa (add ab ab)) dd) rhs (add bb (add aa aa))]
    (s/spec 'signed/qp-square-difference-rearrange [['a signed] ['b signed]]
            (eqv lhs rhs) (ring/ring-eq lhs rhs))))

(def scalar-tangent-spec
  (let [aa (mul 'a 'a) ab (mul 'a 'b) bb (mul 'b 'b) dd (mul (sub 'a 'b) (sub 'a 'b))
        lhs (add (scale aa) ab) rhs (add (scale bb) aa)
        split (add (add (scale aa) (add (scale ab) (scale ab))) (scale dd))
        finish (add (scale bb) (add (scale aa) (scale aa)))
        hsplit (ac lhs (add (scale aa) (add (scale ab) (scale ab))) (scale dd) (scale dd)
                   (ac (scale aa) (scale aa) ab (add (scale ab) (scale ab)) (refl (scale aa))
                       (sym (add (scale ab) (scale ab)) ab (call 'signed/half-scale-add-self ab)))
                   (refl (scale dd)))
        unscaled-left (add (add aa (add ab ab)) dd)
        unscaled-right (add bb (add aa aa))
        [_ collect-left] (collect-scale unscaled-left)
        [_ collect-right] (collect-scale unscaled-right)
        factor-proof (trans split (scale unscaled-left) finish collect-left
                            (trans (scale unscaled-left) (scale unscaled-right) finish
                                   (mc half half unscaled-left unscaled-right (refl half)
                                       (call 'signed/qp-square-difference-rearrange 'a 'b))
                                   (sym finish (scale unscaled-right) collect-right)))
        identity (trans (add lhs (scale dd)) split rhs hsplit
                        (trans split finish rhs factor-proof
                               (ac (scale bb) (scale bb) (add (scale aa) (scale aa)) aa
                                   (refl (scale bb)) (call 'signed/half-scale-add-self aa))))
        hhalf (call 'signed/zero-at-most-of-nonnegative half (call 'nnrat/zero-at-most (f/const* 'nnrat/half [])))
        hsquare (call 'signed/zero-at-most-of-nonnegative dd (call 'signed/square-nonnegative (sub 'a 'b)))
        hterm (lr (mul half s/zero) s/zero (scale dd) (scale dd)
                  (call 'signed/multiply-zero-right half) (refl (scale dd))
                  (call 'signed/multiply-left-monotone half s/zero dd hhalf hsquare))]
    (s/spec 'signed/qp-square-tangent [['a signed] ['b signed]] (le lhs rhs)
            (lr (add lhs s/zero) lhs (add lhs (scale dd)) rhs
                (call 'signed/add-zero-right lhs) identity
                (call 'signed/add-monotone lhs lhs s/zero (scale dd)
                      (call 'signed/at-most-reflexive lhs) hterm)))))

(def gram-tangent-spec
  (let [rx (action 'R 'x 'n) rz (action 'R 'z 'n)
        XX (f/lam [['k nat]] (mul (at rx 'k) (at rx 'k)))
        XZ (f/lam [['k nat]] (mul (at rx 'k) (at rz 'k)))
        ZZ (f/lam [['k nat]] (mul (at rz 'k) (at rz 'k)))
        L (f/lam [['k nat]] (add (scale (at XX 'k)) (at XZ 'k)))
        U (f/lam [['k nat]] (add (scale (at ZZ 'k)) (at XX 'k)))
        xx (quad 'Q 'x 'n) zx (game/payoff 'Q 'z 'x 'n 'n) zz (quad 'Q 'z 'n)
        gram-proof (fn [a b] (call 'signed/qp-gram-bilinear 'Q 'R a b 'n 'gram))
        hxx (gram-proof 'x 'x) hxz (gram-proof 'x 'z) hzz (gram-proof 'z 'z)
        lower (add (scale xx) zx) upper (add (scale zz) xx)
        gl (add (scale (sum XX 'n)) (sum XZ 'n)) gu (add (scale (sum ZZ 'n)) (sum XX 'n))
        lower-eq (ac (scale xx) (scale (sum XX 'n)) zx (sum XZ 'n)
                     (mc half half xx (sum XX 'n) (refl half) hxx) hxz)
        upper-eq (ac (scale zz) (scale (sum ZZ 'n)) xx (sum XX 'n)
                     (mc half half zz (sum ZZ 'n) (refl half) hzz) hxx)]
    (s/spec 'signed/qp-gram-tangent
            [['Q matrix] ['R matrix] ['x family] ['z family] ['n nat] ['gram (gram 'Q 'R 'n)]]
            (le lower upper)
            (lr (sum L 'n) lower (sum U 'n) upper
                (trans (sum L 'n) gl lower (scaled-plus-sum XX XZ 'n) (sym lower gl lower-eq))
                (trans (sum U 'n) gu upper (scaled-plus-sum ZZ XX 'n) (sym upper gu upper-eq))
                (call 'signed/expr-sum-value-monotone-below L U 'n
                      (each 'k 'n (fn [k _] (call 'signed/qp-square-tangent (at rx k) (at rz k)))))))))

(defn sum-three [F G H n]
  (let [FG (f/lam [['t3 nat]] (add (at F 't3) (at G 't3)))
        FGH (f/lam [['t3 nat]] (add (at FG 't3) (at H 't3)))
        mid (add (sum FG n) (sum H n))
        end (add (add (sum F n) (sum G n)) (sum H n))]
    (trans (sum FGH n) mid end (sum-add FG H n)
           (ac (sum FG n) (add (sum F n) (sum G n)) (sum H n) (sum H n)
               (sum-add F G n) (refl (sum H n))))))

(defn stationarity [Q A c x y m n]
  (all-at 'st n (eqv (add (add (game/row Q x n 'st) (at c 'st))
                         (game/column A y m 'st)) s/zero)))

(defn complementary [A b x y m n]
  (all-at 'cp m (eqv (mul (at y 'cp) (sub (at b 'cp) (game/row A x n 'cp))) s/zero)))

(defn feasible [A b z m n]
  (all-at 'pf m (le (game/row A z n 'pf) (at b 'pf))))

(defn nonnegative [y m] (all-at 'yn m (le s/zero (at y 'yn))))

(def stationary-dot-spec
  (let [F (f/lam [['sd nat]] (mul (at 'z 'sd) (game/row 'Q 'x 'n 'sd)))
        G (f/lam [['sd nat]] (mul (at 'c 'sd) (at 'z 'sd)))
        H (f/lam [['sd nat]] (mul (game/column 'A 'y 'm 'sd) (at 'z 'sd)))
        S (f/lam [['sd nat]] (add (add (at F 'sd) (at G 'sd)) (at H 'sd)))
        Z (f/lam [['sd nat]] s/zero)
        qzx (game/payoff 'Q 'z 'x 'n 'n) cz (dot 'c 'z 'n)
        cf (#'game/column-form 'A 'y 'z 'm 'n) p (game/payoff 'A 'y 'z 'm 'n)
        result (add (add qzx cz) p) middle (add (add qzx cz) cf)
        sz (sum-cong S Z 'n (each 'sd 'n (fn [i hi]
             (let [z (at 'z i)
                   st (add (add (game/row 'Q 'x 'n i) (at 'c i)) (game/column 'A 'y 'm i))
                   v (add (add (mul z (game/row 'Q 'x 'n i)) (mul (at 'c i) z)) (mul (game/column 'A 'y 'm i) z))]
               (trans v (mul z st) s/zero (ring/ring-eq v (mul z st))
                      (trans (mul z st) (mul z s/zero) s/zero
                             (mc z z st s/zero (refl z) (at 'stat i hi))
                             (call 'signed/multiply-zero-right z)))))))]
    (s/spec 'signed/qp-stationary-dot
            [['Q matrix] ['A matrix] ['c family] ['x family] ['y family] ['z family] ['m nat] ['n nat]
             ['stat (stationarity 'Q 'A 'c 'x 'y 'm 'n)]]
            (eqv result s/zero)
            (trans result middle s/zero
                   (ac (add qzx cz) (add qzx cz) p cf (refl (add qzx cz))
                       (call 'signed/game-payoff-column-form 'A 'y 'z 'm 'n))
                   (trans middle (sum S 'n) s/zero
                          (sym (sum S 'n) middle (sum-three F G H 'n))
                          (trans (sum S 'n) (sum Z 'n) s/zero sz (call 'signed/expr-sum-value-zero 'n)))))))

(def complementary-product-spec
  (let [yr (mul 'y 'r) yb (mul 'y 'b) slack (mul 'y (sub 'b 'r))]
    (s/spec 'signed/qp-complementary-product
            [['y signed] ['b signed] ['r signed] ['h (eqv slack s/zero)]]
            (eqv yr yb)
            (trans yr (add yr s/zero) yb
                   (sym (add yr s/zero) yr (call 'signed/add-zero-right yr))
                   (trans (add yr s/zero) (add yr slack) yb
                          (ac yr yr s/zero slack (refl yr) (sym slack s/zero 'h))
                          (ring/ring-eq (add yr slack) yb))))))

(def complementary-sum-spec
  (let [F (f/lam [['cs nat]] (mul (at 'y 'cs) (game/row 'A 'x 'n 'cs)))
        G (f/lam [['cs nat]] (mul (at 'y 'cs) (at 'b 'cs)))]
    (s/spec 'signed/qp-complementary-sum
            [['A matrix] ['b family] ['x family] ['y family] ['m nat] ['n nat]
             ['comp (complementary 'A 'b 'x 'y 'm 'n)]]
            (eqv (game/payoff 'A 'y 'x 'm 'n) (dot 'y 'b 'm))
            (sum-cong F G 'm (each 'cs 'm (fn [i hi]
              (call 'signed/qp-complementary-product (at 'y i) (at 'b i) (game/row 'A 'x 'n i)
                    (at 'comp i hi))))))))

(def balance-order-spec
  (let [ap (add 'a 'p) bq (add 'b 'q) aq (add 'a 'q)
        same (trans ap s/zero bq 'ha (sym bq s/zero 'hb))]
    (s/spec 'signed/qp-balance-order
            [['a signed] ['b signed] ['p signed] ['q signed]
             ['ha (eqv ap s/zero)] ['hb (eqv bq s/zero)] ['hq (le 'q 'p)]]
            (le 'a 'b)
            (call 'signed/at-most-add-right-cancel 'a 'b 'q
                  (lr aq aq ap bq (refl aq) same
                      (call 'signed/add-monotone 'a 'a 'q 'p (call 'signed/at-most-reflexive 'a) 'hq))))))

(def combine-spec
  (let [a (add (scale 'xx) 'zx) b (add (scale 'zz) 'xx)
        c (add 'xx 'cx) d (add 'zx 'cz)
        lhs (add (scale 'xx) 'cx) rhs (add (scale 'zz) 'cz) shared (add 'zx 'xx)]
    (s/spec 'signed/qp-combine-bounds
            [['xx signed] ['zx signed] ['zz signed] ['cx signed] ['cz signed]
             ['tangent (le a b)] ['linear (le c d)]]
            (le lhs rhs)
            (call 'signed/at-most-add-right-cancel lhs rhs shared
                  (lr (add a c) (add lhs shared) (add b d) (add rhs shared)
                      (ring/ring-eq (add a c) (add lhs shared))
                      (ring/ring-eq (add b d) (add rhs shared))
                      (call 'signed/add-monotone a b c d 'tangent 'linear))))))

(def kkt-spec
  (let [xx (quad 'Q 'x 'n) zx (game/payoff 'Q 'z 'x 'n 'n) zz (quad 'Q 'z 'n)
        cx (dot 'c 'x 'n) cz (dot 'c 'z 'n)
        p (game/payoff 'A 'y 'x 'm 'n) q (game/payoff 'A 'y 'z 'm 'n) yb (dot 'y 'b 'm)
        hp (call 'signed/qp-complementary-sum 'A 'b 'x 'y 'm 'n 'comp)
        hq (lr q q yb p (refl q) (sym p yb hp)
               (call 'signed/expr-sum-value-weighted-monotone-left 'y (action 'A 'z 'n) 'b 'm 'yn 'feasible))
        hx (call 'signed/qp-stationary-dot 'Q 'A 'c 'x 'y 'x 'm 'n 'stat)
        hz (call 'signed/qp-stationary-dot 'Q 'A 'c 'x 'y 'z 'm 'n 'stat)]
    (s/spec 'signed/expr-sum-qp-kkt-optimal
            [['Q matrix] ['R matrix] ['A matrix] ['b family] ['c family] ['x family] ['y family]
             ['m nat] ['n nat] ['gram (gram 'Q 'R 'n)] ['stat (stationarity 'Q 'A 'c 'x 'y 'm 'n)]
             ['comp (complementary 'A 'b 'x 'y 'm 'n)] ['yn (nonnegative 'y 'm)]
             ['z family] ['feasible (feasible 'A 'b 'z 'm 'n)]]
            (le (objective 'Q 'c 'x 'n) (objective 'Q 'c 'z 'n))
            (call 'signed/qp-combine-bounds xx zx zz cx cz
                  (call 'signed/qp-gram-tangent 'Q 'R 'x 'z 'n 'gram)
                  (call 'signed/qp-balance-order (add xx cx) (add zx cz) p q hx hz hq)))))

(defn conjunction [ps]
  (if (= 1 (count ps)) (first ps) (call 'proposition/conjunction (first ps) (conjunction (rest ps)))))

(defn extract [ps i proof]
  (if (= 1 (count ps)) proof
      (if (zero? i) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec i) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [gram-action-spec gram-bilinear-spec square-difference-spec scalar-tangent-spec gram-tangent-spec stationary-dot-spec complementary-product-spec complementary-sum-spec balance-order-spec combine-spec kkt-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      ring/extend-environment
      game/extend-environment
      bb/extend-environment
      norm-nn/extend-environment
      order-cancel/extend-environment
      (support/extend-with :expr-sum-qp-kkt theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
