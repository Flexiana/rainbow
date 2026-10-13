(ns rainbow.math.lemmas.vickrey-dsic
  "General lemmas: vickrey dsic. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.one-center :as center :refer [eq-ind]]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.finite.rational-argmax :as argmax]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn explode [goal h] (call 'proposition/explode goal h))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn eqn [x y] (f/equality type-level nat x y))

(defn neqn [x y] (call 'proposition/negation (eqn x y)))

(defn eqb [x y] (f/equality type-level bool x y))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(defn one-of [y h]
  (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
           [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero h))]
           [one (ring (sub one s/zero) one)]))

(defn zero-mul [x y h] (trans (mul x y) (mul s/zero y) s/zero (mcong x s/zero y y h (refl y)) (call 'signed/multiply-zero-left y)))

(defn one-mul [x y h] (trans (mul x y) (mul one y) y (mcong x one y y h (refl y)) (one-times y)))

(defn by-bit [D goal-of on-false on-true hname]
  (f/app (f/const* 'data/Bool.rec [prop-level])
         (f/lam [['bb bool]] (f/forall [[hname (eqb D 'bb)]] (goal-of 'bb)))
         (f/lam [[hname (eqb D bfalse)]] (on-false hname))
         (f/lam [[hname (eqb D btrue)]] (on-true hname))
         D
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn winner-bid [b w n] (sum (f/lam [['wb nat]] (mul (at w 'wb) (at b 'wb))) n))

(defn indicators [b w p] (f/lam [['ai nat]] (mul (sub one (at w 'ai)) (eq-ind (at b 'ai) p))))

(defn outcome-binders [b w p n tag]
  (let [h (fn [k] (symbol (str tag k)))]
    [[(h "w01") (s/all-below n #(zero-one (at w %)))]
     [(h "sum") (eqv (sum (f/lam [['ws nat]] (at w 'ws)) n) one)]
     [(h "win") (s/all-below n #(le (at b %) (winner-bid b w n)))]
     [(h "lose") (s/all-below n #(le (mul (sub one (at w %)) (at b %)) p))]
     [(h "att") (le one (sum (indicators b w p) n))]]))

(defn w-nn [w h i hi] (call 'signed/zero-one-nonnegative (at w i) (at h i hi)))

(def others-lose-spec
  (let [w 'w n 'n W (sum (f/lam [['ws nat]] (at w 'ws)) n)
        hnn (f/lam [['nj nat] ['nj-lt (below 'nj n)]] (w-nn w 'hw01 'nj 'nj-lt))
        two (call 'signed/expr-sum-value-two-distinct-bound w n hnn 'j 'j-lt 'i 'i-lt 'hne)       ; w_j + w_i <= W
        wj-le (le-resp (add (at w 'j) one) (add (at w 'j) one) W one (refl (add (at w 'j) one)) 'hsum
                       (le-resp (add (at w 'j) (at w 'i)) (add (at w 'j) one) W W
                                (s/add-cong (at w 'j) (at w 'j) (at w 'i) one (refl (at w 'j)) 'hwi) (refl W) two))
        np (le-resp (add (add (at w 'j) one) (neg one)) (at w 'j) (add one (neg one)) s/zero
                    (ring (add (add (at w 'j) one) (neg one)) (at w 'j)) (ring (add one (neg one)) s/zero)
                    (call 'signed/add-right-monotone (add (at w 'j) one) one (neg one) wj-le))]
    (s/spec 'signed/vickrey-others-lose
            [['w family] ['n nat] ['hw01 (s/all-below n #(zero-one (at w %)))] ['hsum (eqv W one)]
             ['i nat] ['i-lt (below 'i n)] ['hwi (eqv (at w 'i) one)] ['j nat] ['j-lt (below 'j n)] ['hne (neqn 'j 'i)]]
            (eqv (at w 'j) s/zero)
            (anti (at w 'j) s/zero np (w-nn w 'hw01 'j 'j-lt)))))

(def winner-bid-spec
  (let [b 'b w 'w n 'n W (sum (f/lam [['ws nat]] (at w 'ws)) n) bi (at b 'i)
        T (f/lam [['tj nat]] (mul (at w 'tj) (sub (at b 'tj) bi)))
        Z (f/lam [['tz nat]] s/zero)
        term (fn [j hj]
               (let [goal (eqv (at T j) s/zero)]
                 (by-bit (call 'nat/decide-equality j 'i) (fn [_] goal)
                         (fn [hb] (let [ne (f/lam [['je (eqn j 'i)]]
                                                  (call 'bool/false-not-true
                                                        (f/app (f/const* 'equality/transitive [type-level]) bool bfalse (call 'nat/decide-equality j 'i) btrue
                                                               (f/app (f/const* 'equality/symmetric [type-level]) bool (call 'nat/decide-equality j 'i) bfalse hb)
                                                               (subst-nat 'i j (f/app (f/const* 'equality/symmetric [type-level]) nat j 'i 'je)
                                                                          (f/lam [['sd nat]] (eqb (call 'nat/decide-equality 'sd 'i) btrue))
                                                                          (call 'nat/decide-equality-reflexive-true 'i)))))]
                                    (zero-mul (at w j) (sub (at b j) bi) (call 'signed/vickrey-others-lose w n 'hw01 'hsum 'i 'i-lt 'hwi j hj ne))))
                         (fn [hb] (let [je (call 'nat/decide-equality-true-sound j 'i hb)]
                                    (trans (at T j) (mul (at w j) s/zero) s/zero
                                           (mcong (at w j) (at w j) (sub (at b j) bi) s/zero (refl (at w j))
                                                  (subst-nat 'i j (f/app (f/const* 'equality/symmetric [type-level]) nat j 'i je) (f/lam [['sj nat]] (eqv (sub (at b 'sj) bi) s/zero)) (ring (sub bi bi) s/zero)))
                                           (call 'signed/multiply-zero-right (at w j)))))
                         'wh)))
        WB (f/lam [['wb nat]] (mul (at w 'wb) (at b 'wb)))
        WI (f/lam [['wi nat]] (mul (at w 'wi) bi))
        t-sum (a/chain (sum T n)
                       [(sum (f/lam [['d1 nat]] (sub (at WB 'd1) (at WI 'd1))) n)
                        (a/sum-cong T (f/lam [['d1 nat]] (sub (at WB 'd1) (at WI 'd1))) n 'va (fn [j _] (call 'signed/multiply-subtract-expand (at w j) (at b j) bi)))]
                       [(sub (sum WB n) (sum WI n)) (call 'signed/expr-sum-value-subtract WB WI n)]
                       [(sub (sum WB n) bi) (s/add-cong (sum WB n) (sum WB n) (neg (sum WI n)) (neg bi) (refl (sum WB n))
                                                        (a/neg-cong (sum WI n) bi (a/chain (sum WI n) [(mul W bi) (sym (mul W bi) (sum WI n) (call 'signed/expr-sum-value-scale-right (f/lam [['ws nat]] (at w 'ws)) bi n))]
                                                                                           [(mul one bi) (mcong W one bi bi 'hsum (refl bi))] [bi (one-times bi)])))])
        zero (trans (sum T n) (sum Z n) s/zero (a/sum-cong T Z n 'vb (fn [j hj] (term j hj))) (call 'signed/expr-sum-value-zero n))]
    (s/spec 'signed/vickrey-winner-bid
            [['b family] ['w family] ['n nat] ['hw01 (s/all-below n #(zero-one (at w %)))] ['hsum (eqv W one)]
             ['i nat] ['i-lt (below 'i n)] ['hwi (eqv (at w 'i) one)]]
            (eqv (winner-bid b w n) bi)
            (a/chain (winner-bid b w n) [(add (sub (sum WB n) bi) bi) (ring (sum WB n) (add (sub (sum WB n) bi) bi))]
                     [(add s/zero bi) (s/add-cong (sub (sum WB n) bi) s/zero bi bi (trans (sub (sum WB n) bi) (sum T n) s/zero (sym (sum T n) (sub (sum WB n) bi) t-sum) zero) (refl bi))]
                     [bi (ring (add s/zero bi) bi)]))))

(def price-bound-spec
  (let [b 'b w 'w p 'p n 'n R 'R I (indicators b w p) SI (sum I n)
        per (fn [j hj]
              (let [wj (at w j) l (sub one wj) e (eq-ind (at b j) p) Ij (mul l e) goal (le (mul Ij p) (mul Ij R))
                    both-zero (fn [hz] (a/eq-le (mul Ij p) (mul Ij R) (trans (mul Ij p) s/zero (mul Ij R) (zero-mul Ij p hz) (sym (mul Ij R) s/zero (zero-mul Ij R hz)))))]
                (cases (eqv wj s/zero) (eqv (sub one wj) s/zero) goal (call 'signed/multiply-zero-split wj (sub one wj) (at 'hw01 j hj))
                       (f/lam [['lz (eqv wj s/zero)]]
                              (let [l1 (a/chain l [(sub one s/zero) (s/add-cong one one (neg wj) (neg s/zero) (refl one) (a/neg-cong wj s/zero 'lz))] [one (ring (sub one s/zero) one)])]
                                (cases (eqv e s/zero) (pconj (eqv e one) (eqv (at b j) p)) goal (call 'signed/eq-indicator-cases (at b j) p)
                                       (f/lam [['ez (eqv e s/zero)]] (both-zero (trans Ij (mul l s/zero) s/zero (mcong l l e s/zero (refl l) 'ez) (call 'signed/multiply-zero-right l))))
                                       (f/lam [['eo (pconj (eqv e one) (eqv (at b j) p))]]
                                              (let [I1 (trans Ij (mul one one) one (mcong l one e one l1 (pleft (eqv e one) (eqv (at b j) p) 'eo)) (one-times one))]
                                                (le-resp (mul one p) (mul Ij p) (mul one R) (mul Ij R) (mcong one Ij p p (sym Ij one I1) (refl p)) (mcong one Ij R R (sym Ij one I1) (refl R))
                                                         (le-resp p (mul one p) R (mul one R) (sym (mul one p) p (one-times p)) (sym (mul one R) R (one-times R))
                                                                  (le-resp (at b j) p R R (pright (eqv e one) (eqv (at b j) p) 'eo) (refl R) (at 'hR j hj 'lz)))))))))
                       (f/lam [['lo (eqv (sub one wj) s/zero)]] (both-zero (zero-mul l e 'lo))))))
        IP (f/lam [['ip nat]] (mul (at I 'ip) p)) IR (f/lam [['ir nat]] (mul (at I 'ir) R))
        summed (le-resp (sum IP n) (mul p SI) (sum IR n) (mul R SI)
                        (a/chain (sum IP n) [(mul SI p) (sym (mul SI p) (sum IP n) (call 'signed/expr-sum-value-scale-right I p n))] [(mul p SI) (call 'signed/multiply-commutative SI p)])
                        (a/chain (sum IR n) [(mul SI R) (sym (mul SI R) (sum IR n) (call 'signed/expr-sum-value-scale-right I R n))] [(mul R SI) (call 'signed/multiply-commutative SI R)])
                        (a/sum-mono IP IR n 'pa (fn [j hj] (per j hj))))]
    (s/spec 'signed/vickrey-price-bound
            [['b family] ['w family] ['p signed] ['n nat] ['hw01 (s/all-below n #(zero-one (at w %)))] ['hatt (le one SI)]
             ['R signed] ['hR (f/forall [['rj nat] ['rj-lt (below 'rj n)] ['rz (eqv (at w 'rj) s/zero)]] (le (at b 'rj) R))]]
            (le p R)
            (call 'signed/at-most-cancel-positive-right p R SI
                  (call 'signed/less-than-of-less-than-of-at-most s/zero one SI (f/const* 'signed/zero-less-than-one []) 'hatt)
                  summed))))

(def loser-below-spec
  (let [b 'b w 'w p 'p n 'n wj0 (call 'signed/vickrey-others-lose w n 'hw01 'hsum 'i 'i-lt 'hwi 'j 'j-lt 'hne)
        l (sub one (at w 'j))]
    (s/spec 'signed/vickrey-others-below-price
            [['b family] ['w family] ['p signed] ['n nat] ['hw01 (s/all-below n #(zero-one (at w %)))] ['hsum (eqv (sum (f/lam [['ws nat]] (at w 'ws)) n) one)]
             ['hlose (s/all-below n #(le (mul (sub one (at w %)) (at b %)) p))]
             ['i nat] ['i-lt (below 'i n)] ['hwi (eqv (at w 'i) one)] ['j nat] ['j-lt (below 'j n)] ['hne (neqn 'j 'i)]]
            (le (at b 'j) p)
            (le-resp (mul l (at b 'j)) (at b 'j) p p
                     (one-mul l (at b 'j) (a/chain l [(sub one s/zero) (s/add-cong one one (neg (at w 'j)) (neg s/zero) (refl one) (a/neg-cong (at w 'j) s/zero wj0))] [one (ring (sub one s/zero) one)]))
                     (refl p) (at 'hlose 'j 'j-lt)))))

(def dsic-spec
  (let [b1 'b1 w1 'w1 p1 'p1 b2 'b2 w2 'w2 p2 'p2 n 'n i 'i v (at b1 'i)
        lhs (mul (at w2 i) (sub v p2)) rhs (mul (at w1 i) (sub v p1)) goal (le lhs rhs)
        ;; j with w_j ~ c and w_i ~ d, c /~ d  ->  j /= i
        differ (fn [w j cj ci hj hi contra]
                 (f/lam [['de (eqn j 'i)]]
                        (contra (subst-nat j 'i 'de (f/lam [['sd nat]] (eqv (at w 'sd) cj)) hj) hi)))
        one-zero (fn [x h1 h0] (call 'signed/one-not-equivalent-zero (trans one x s/zero (sym x one h1) h0)))
        zero-one* (fn [x h0 h1] (call 'signed/one-not-equivalent-zero (trans one x s/zero (sym x one h1) h0)))
        v-p1-nn (fn [w1i] ; w1_i ~ 1  ->  0 <= v - p1
                  (let [p1v (call 'signed/vickrey-price-bound b1 w1 p1 n 'h1w01 'h1att v
                                  (f/lam [['rj nat] ['rj-lt (below 'rj n)] ['rz (eqv (at w1 'rj) s/zero)]]
                                         (le-resp (at b1 'rj) (at b1 'rj) (winner-bid b1 w1 n) v (refl (at b1 'rj))
                                                  (call 'signed/vickrey-winner-bid b1 w1 n 'h1w01 'h1sum i 'i-lt w1i) (at 'h1win 'rj 'rj-lt))))]
                    (le-resp (sub p1 p1) s/zero (sub v p1) (sub v p1) (ring (sub p1 p1) s/zero) (refl (sub v p1))
                             (call 'signed/add-right-monotone p1 v (neg p1) p1v))))]
    (s/spec 'signed/vickrey-truthful-dominant
            (-> [['b1 family] ['w1 family] ['p1 signed] ['b2 family] ['w2 family] ['p2 signed] ['n nat]]
                (into (outcome-binders b1 w1 p1 n "h1")) (into (outcome-binders b2 w2 p2 n "h2"))
                (into [['i nat] ['i-lt (below 'i n)]
                       ['hsame (f/forall [['sj nat] ['sj-lt (below 'sj n)] ['sne (neqn 'sj 'i)]] (eqv (at b1 'sj) (at b2 'sj)))]]))
            goal
            (cases (eqv (at w2 i) s/zero) (eqv (sub one (at w2 i)) s/zero) goal (call 'signed/multiply-zero-split (at w2 i) (sub one (at w2 i)) (at 'h2w01 i 'i-lt))
                   ;; i loses the deviation: utility 0 <= the truthful utility
                   (f/lam [['d0 (eqv (at w2 i) s/zero)]]
                          (le-resp s/zero lhs rhs rhs (sym lhs s/zero (zero-mul (at w2 i) (sub v p2) 'd0)) (refl rhs)
                                   (cases (eqv (at w1 i) s/zero) (eqv (sub one (at w1 i)) s/zero) (le s/zero rhs) (call 'signed/multiply-zero-split (at w1 i) (sub one (at w1 i)) (at 'h1w01 i 'i-lt))
                                          (f/lam [['t0 (eqv (at w1 i) s/zero)]] (a/eq-le s/zero rhs (sym rhs s/zero (zero-mul (at w1 i) (sub v p1) 't0))))
                                          (f/lam [['t1 (eqv (sub one (at w1 i)) s/zero)]]
                                                 (let [w1i (one-of (at w1 i) 't1)]
                                                   (le-resp s/zero s/zero (sub v p1) rhs (refl s/zero) (sym rhs (sub v p1) (one-mul (at w1 i) (sub v p1) w1i)) (v-p1-nn w1i)))))))
                   ;; i wins the deviation, paying p2 >= every other bid
                   (f/lam [['d1 (eqv (sub one (at w2 i)) s/zero)]]
                          (let [w2i (one-of (at w2 i) 'd1)
                                lhs-eq (one-mul (at w2 i) (sub v p2) w2i)
                                other-le-p2 (fn [j hj ne] (le-resp (at b2 j) (at b1 j) p2 p2 (sym (at b1 j) (at b2 j) (at 'hsame j hj ne)) (refl p2)
                                                                   (call 'signed/vickrey-others-below-price b2 w2 p2 n 'h2w01 'h2sum 'h2lose i 'i-lt w2i j hj ne)))]
                            (le-resp (sub v p2) lhs rhs rhs (sym lhs (sub v p2) lhs-eq) (refl rhs)
                                     (cases (eqv (at w1 i) s/zero) (eqv (sub one (at w1 i)) s/zero) (le (sub v p2) rhs) (call 'signed/multiply-zero-split (at w1 i) (sub one (at w1 i)) (at 'h1w01 i 'i-lt))
                                            ;; truthful i lost: v <= the winner's bid <= p2, so v - p2 <= 0 = rhs
                                            (f/lam [['t0 (eqv (at w1 i) s/zero)]]
                                                   (let [W1 (sum (f/lam [['ws nat]] (at w1 'ws)) n)
                                                         WP (f/lam [['wp nat]] (mul (at w1 'wp) p2))
                                                         wb-le (le-resp (winner-bid b1 w1 n) (winner-bid b1 w1 n) (sum WP n) p2 (refl (winner-bid b1 w1 n))
                                                                        (a/chain (sum WP n) [(mul W1 p2) (sym (mul W1 p2) (sum WP n) (call 'signed/expr-sum-value-scale-right (f/lam [['ws nat]] (at w1 'ws)) p2 n))]
                                                                                 [(mul one p2) (mcong W1 one p2 p2 'h1sum (refl p2))] [p2 (one-times p2)])
                                                                        (a/sum-mono (f/lam [['wb nat]] (mul (at w1 'wb) (at b1 'wb))) WP n 'da
                                                                                    (fn [j hj]
                                                                                      (cases (eqv (at w1 j) s/zero) (eqv (sub one (at w1 j)) s/zero) (le (mul (at w1 j) (at b1 j)) (mul (at w1 j) p2))
                                                                                             (call 'signed/multiply-zero-split (at w1 j) (sub one (at w1 j)) (at 'h1w01 j hj))
                                                                                             (f/lam [['j0 (eqv (at w1 j) s/zero)]]
                                                                                                    (a/eq-le (mul (at w1 j) (at b1 j)) (mul (at w1 j) p2)
                                                                                                             (trans (mul (at w1 j) (at b1 j)) s/zero (mul (at w1 j) p2) (zero-mul (at w1 j) (at b1 j) 'j0) (sym (mul (at w1 j) p2) s/zero (zero-mul (at w1 j) p2 'j0)))))
                                                                                             (f/lam [['j1 (eqv (sub one (at w1 j)) s/zero)]]
                                                                                                    (let [w1j (one-of (at w1 j) 'j1)
                                                                                                          ne (differ w1 j one s/zero w1j 't0 (fn [h1 h0] (one-zero (at w1 i) h1 h0)))]
                                                                                                      (lmono (at w1 j) (at b1 j) p2 (call 'signed/zero-one-nonnegative (at w1 j) (at 'h1w01 j hj))
                                                                                                             (other-le-p2 j hj ne))))))))
                                                         v-le (le-trans v (winner-bid b1 w1 n) p2 (at 'h1win i 'i-lt) wb-le)]
                                                     (le-resp (sub v p2) (sub v p2) s/zero rhs (refl (sub v p2)) (sym rhs s/zero (zero-mul (at w1 i) (sub v p1) 't0))
                                                              (le-resp (sub v p2) (sub v p2) (sub p2 p2) s/zero (refl (sub v p2)) (ring (sub p2 p2) s/zero)
                                                                       (call 'signed/add-right-monotone v p2 (neg p2) v-le)))))
                                            ;; truthful i won too: p1 <= p2, so v - p2 <= v - p1 = rhs
                                            (f/lam [['t1 (eqv (sub one (at w1 i)) s/zero)]]
                                                   (let [w1i (one-of (at w1 i) 't1)
                                                         p1-le (call 'signed/vickrey-price-bound b1 w1 p1 n 'h1w01 'h1att p2
                                                                     (f/lam [['rj nat] ['rj-lt (below 'rj n)] ['rz (eqv (at w1 'rj) s/zero)]]
                                                                            (other-le-p2 'rj 'rj-lt (differ w1 'rj s/zero one 'rz w1i (fn [h0 h1] (zero-one* (at w1 i) h0 h1))))))]
                                                     (le-resp (sub v p2) (sub v p2) (sub v p1) rhs (refl (sub v p2)) (sym rhs (sub v p1) (one-mul (at w1 i) (sub v p1) w1i))
                                                              (call 'signed/add-left-monotone (neg p2) (neg p1) v (call 'signed/at-most-negate p1 p2 p1-le)))))))))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body tag]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" tag "-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(def borrowed-specs [kmeans/zero-one-nonneg-spec two-terms/two-distinct-bound-spec indep/subtract-expand-spec
                     cpm/negate-le-spec])

(def theorem-specs [others-lose-spec winner-bid-spec price-bound-spec loser-below-spec dsic-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env center/extend-environment nonneg-zero/extend-environment add-monotone/extend-environment multiply-monotone/extend-environment multiply-ring/extend-environment dot-negate/extend-environment two-terms/extend-environment argmax/extend-environment (support/extend-with-shared :expr-sum-vickrey-dsic borrowed-specs) (support/extend-with-shared :expr-sum-vickrey-dsic theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.vickrey-dsic))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
