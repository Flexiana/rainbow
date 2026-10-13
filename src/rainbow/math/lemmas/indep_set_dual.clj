(ns rainbow.math.lemmas.indep-set-dual
  "General lemmas: indep set dual. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.limit-uniqueness :as limit-uniqueness]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn assoc3 [x y z] (call 'signed/multiply-associative x y z))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn left-commute [x y z]
  (a/chain (mul x (mul y z)) [(mul (mul x y) z) (sym (mul (mul x y) z) (mul x (mul y z)) (assoc3 x y z))]
           [(mul (mul y x) z) (mcong (mul x y) (mul y x) z z (comm x y) (refl z))]
           [(mul y (mul x z)) (assoc3 y x z)]))

(defn pull-middle [x m w]
  (a/chain (mul (mul x m) w) [(mul x (mul m w)) (assoc3 x m w)] [(mul m (mul x w)) (left-commute x m w)]))

(defn swap-tail [z m q]
  (a/chain (mul (mul z m) q) [(mul z (mul m q)) (assoc3 z m q)]
           [(mul z (mul q m)) (mcong z z (mul m q) (mul q m) (refl z) (comm m q))]
           [(mul (mul z q) m) (sym (mul (mul z q) m) (mul z (mul q m)) (assoc3 z q m))]))

(defn eq-bool [l r] (f/equality type-level bool l r))

(defn decide-le [x y] (call 'signed/decide-at-most x y))

(def total-spec
  (let [goal (disj (le 'a 'b) (le 'b 'a))
        d (decide-le 'a 'b)]
    (s/spec 'signed/at-most-total [['a signed] ['b signed]]
            goal
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['tv bool]] (f/forall [['th (eq-bool d 'tv)]] goal))
                          (f/lam [['tf (eq-bool d (f/const* 'data/false []))]]
                                 (call 'proposition/right-disjunct (le 'a 'b) (le 'b 'a)
                                       (call 'signed/decide-at-most-false-reverse 'a 'b 'tf)))
                          (f/lam [['tt (eq-bool d (f/const* 'data/true []))]]
                                 (call 'proposition/left-disjunct (le 'a 'b) (le 'b 'a)
                                       (call 'signed/decide-at-most-true-sound 'a 'b 'tt)))
                          d)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool d)))))

(def one-minus-spec
  (s/spec 'signed/one-minus-nonnegative [['a signed] ['h (le 'a one)]]
          (le s/zero (sub one 'a))
          (le-resp (add 'a (neg 'a)) s/zero (add one (neg 'a)) (sub one 'a)
                   (ring (add 'a (neg 'a)) s/zero) (refl (sub one 'a))
                   (call 'signed/add-right-monotone 'a one (neg 'a) 'h))))

(def zero-one-upper-spec
  (s/spec 'signed/zero-one-at-most-one [['x signed] ['h (eqv (mul 'x (sub one 'x)) s/zero)]]
          (le 'x one)
          (cases (eqv 'x s/zero) (eqv (sub one 'x) s/zero) (le 'x one)
                 (call 'signed/multiply-zero-split 'x (sub one 'x) 'h)
                 (f/lam [['hx (eqv 'x s/zero)]] (le-resp s/zero 'x one one (sym 'x s/zero 'hx) (refl one) zero-le-one))
                 (f/lam [['h1 (eqv (sub one 'x) s/zero)]]
                        (a/eq-le 'x one
                                 (a/chain 'x [(sub one (sub one 'x)) (ring 'x (sub one (sub one 'x)))]
                                          [(sub one s/zero) (s/add-cong one one (neg (sub one 'x)) (neg s/zero) (refl one)
                                                                        (a/neg-cong (sub one 'x) s/zero 'h1))]
                                          [one (ring (sub one s/zero) one)]))))))

(def subtract-expand-spec
  (s/spec 'signed/multiply-subtract-expand [['p signed] ['q signed] ['t signed]]
          (eqv (mul 'p (sub 'q 't)) (add (mul 'p 'q) (neg (mul 'p 't))))
          (trans (mul 'p (sub 'q 't)) (add (mul 'p 'q) (mul 'p (neg 't))) (add (mul 'p 'q) (neg (mul 'p 't)))
                 (call 'signed/multiply-distributes-add-left 'p 'q (neg 't))
                 (s/add-cong (mul 'p 'q) (mul 'p 'q) (mul 'p (neg 't)) (neg (mul 'p 't)) (refl (mul 'p 'q))
                             (call 'signed/multiply-negate-right 'p 't)))))

(def square-bound-spec
  (s/spec 'signed/square-at-most-self-at-most-one [['s signed] ['h0 (le s/zero 's)] ['h (le (mul 's 's) 's)]]
          (le 's one)
          (cases (le 's one) (le one 's) (le 's one) (call 'signed/at-most-total 's one)
                 (f/lam [['hl (le 's one)]] 'hl)
                 (f/lam [['hg (le one 's)]]
                        (let [grow (le-resp (mul 's one) 's (mul 's 's) (mul 's 's) (times-one 's) (refl (mul 's 's))
                                            (lmono 's one 's 'h0 'hg))
                              same (call 'signed/at-most-antisymmetric (mul 's 's) 's 'h grow)
                              product (a/chain (mul 's (sub 's one))
                                               [(add (mul 's 's) (neg (mul 's one))) (call 'signed/multiply-subtract-expand 's 's one)]
                                               [(add (mul 's 's) (neg 's)) (s/add-cong (mul 's 's) (mul 's 's) (neg (mul 's one)) (neg 's)
                                                                                       (refl (mul 's 's)) (a/neg-cong (mul 's one) 's (times-one 's)))]
                                               [(add 's (neg 's)) (s/add-cong (mul 's 's) 's (neg 's) (neg 's) same (refl (neg 's)))]
                                               [s/zero (ring (add 's (neg 's)) s/zero)])]
                          (cases (eqv 's s/zero) (eqv (sub 's one) s/zero) (le 's one)
                                 (call 'signed/multiply-zero-split 's (sub 's one) product)
                                 (f/lam [['hs (eqv 's s/zero)]] (le-resp s/zero 's one one (sym 's s/zero 'hs) (refl one) zero-le-one))
                                 (f/lam [['hs1 (eqv (sub 's one) s/zero)]]
                                        (a/eq-le 's one
                                                 (a/chain 's [(add (sub 's one) one) (ring 's (add (sub 's one) one))]
                                                          [(add s/zero one) (s/add-cong (sub 's one) s/zero one one 'hs1 (refl one))]
                                                          [one (ring (add s/zero one) one)])))))))))

(def split-at-spec
  (s/spec 'signed/multiply-split-at [['y signed] ['t signed] ['a signed]]
          (eqv (mul 'y 't) (add (mul 'y 'a) (mul 'y (sub 't 'a))))
          (trans (mul 'y 't) (mul 'y (add 'a (sub 't 'a))) (add (mul 'y 'a) (mul 'y (sub 't 'a)))
                 (mcong 'y 'y 't (add 'a (sub 't 'a)) (refl 'y) (ring 't (add 'a (sub 't 'a))))
                 (call 'signed/multiply-distributes-add-left 'y 'a (sub 't 'a)))))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn clique-term [A M C u v] (mul (at M C u) (mul (at M C v) (sub one (at A u v)))))

(defn indep-term [A z u v] (mul (at z u) (mul (at z v) (at A u v))))

(defn clique-rows [A M C n] (s/all-below n (fn [u] (le (sum (f/lam [['kv nat]] (clique-term A M C u 'kv)) n) s/zero))))

(defn indep-rows [A z n] (s/all-below n (fn [u] (le (sum (f/lam [['iv nat]] (indep-term A z u 'iv)) n) (at z u)))))

(defn unit-interval [z n] [(s/all-below n #(le s/zero (at z %))) (s/all-below n #(le (at z %) one))])

(defn meet [z M C n] (sum (f/lam [['mv nat]] (mul (at z 'mv) (at M C 'mv))) n))

(def counting-spec
  (let [[z-lo z-hi] (unit-interval 'z 'n)
        [m-lo m-hi] (unit-interval (f/lam [['rv nat]] (at 'M 'C 'rv)) 'n)
        p (fn [v] (mul (at 'z v) (at 'M 'C v)))
        S (meet 'z 'M 'C 'n)
        Mu (fn [u] (at 'M 'C u))
        per-u
        (fn [u hu]
          (let [I (fn [v] (indep-term 'A 'z u v))
                K (fn [v] (clique-term 'A 'M 'C u v))
                c (fn [v] (sub one (at 'A u v)))
                ;; (z_u M_u)(z_v M_v) ~ (z_u M_u)((z_v M_v) A) + (z_u M_u)((z_v M_v)(1 - A))
                T1 (fn [v] (mul (p u) (mul (p v) (at 'A u v))))
                T2 (fn [v] (mul (p u) (mul (p v) (c v))))
                F1 (f/lam [['f1 nat]] (T1 'f1)) F2 (f/lam [['f2 nat]] (T2 'f2))
                FP (f/lam [['fp nat]] (mul (p u) (p 'fp)))
                FS (f/lam [['fs nat]] (add (T1 'fs) (T2 'fs)))
                G1 (f/lam [['g1 nat]] (mul (Mu u) (I 'g1)))
                G2 (f/lam [['g2 nat]] (mul (at 'z u) (K 'g2)))
                IS (f/lam [['is nat]] (I 'is)) KS (f/lam [['ks nat]] (K 'ks))
                hzu (at 'hz0 u hu) hMu (at 'hM0 u hu)
                split (trans (sum FP 'n) (sum FS 'n) (add (sum F1 'n) (sum F2 'n))
                             (a/sum-cong FP FS 'n 'sv
                                         (fn [v _]
                                           (let [al (p u) be (p v) ba (mul be (at 'A u v)) bc (mul be (c v))]
                                             (a/chain (mul al be)
                                                      [(mul al (mul be one)) (mcong al al be (mul be one) (refl al) (sym (mul be one) be (times-one be)))]
                                                      [(mul al (add ba bc)) (mcong al al (mul be one) (add ba bc) (refl al)
                                                                                   (call 'signed/multiply-split-at be one (at 'A u v)))]
                                                      [(add (T1 v) (T2 v)) (call 'signed/multiply-distributes-add-left al ba bc)]))))
                             (call 'signed/expr-sum-value-add F1 F2 'n))
                b1 (le-trans (sum F1 'n) (sum G1 'n) (mul (Mu u) (at 'z u))
                             (a/sum-mono F1 G1 'n 'tv
                                         (fn [v hv]
                                           (let [ba (mul (p v) (at 'A u v)) za (mul (at 'z v) (at 'A u v))
                                                 inner (le-resp (mul za (Mu v)) ba (mul za one) za
                                                                (sym ba (mul za (Mu v)) (swap-tail (at 'z v) (Mu v) (at 'A u v)))
                                                                (times-one za)
                                                                (lmono za (Mu v) one (nonneg-prod (at 'z v) (at 'A u v) (at 'hz0 v hv) (at 'hA0 u hu v hv))
                                                                       (at 'hM1 v hv)))]
                                             (le-resp (mul (Mu u) (mul (at 'z u) ba)) (T1 v) (mul (Mu u) (I v)) (mul (Mu u) (I v))
                                                      (sym (T1 v) (mul (Mu u) (mul (at 'z u) ba)) (pull-middle (at 'z u) (Mu u) ba))
                                                      (refl (mul (Mu u) (I v)))
                                                      (lmono (Mu u) (mul (at 'z u) ba) (I v) hMu (lmono (at 'z u) ba za hzu inner))))))
                             (le-resp (mul (Mu u) (sum IS 'n)) (sum G1 'n) (mul (Mu u) (at 'z u)) (mul (Mu u) (at 'z u))
                                      (call 'signed/expr-sum-value-scale-left IS (Mu u) 'n) (refl (mul (Mu u) (at 'z u)))
                                      (lmono (Mu u) (sum IS 'n) (at 'z u) hMu (at 'hind u hu))))
                b2 (le-trans (sum F2 'n) (sum G2 'n) s/zero
                             (a/sum-mono F2 G2 'n 'uv
                                         (fn [v hv]
                                           (let [hK (nonneg-prod (Mu u) (mul (Mu v) (c v)) hMu
                                                                 (nonneg-prod (Mu v) (c v) (at 'hM0 v hv)
                                                                              (call 'signed/one-minus-nonnegative (at 'A u v) (at 'hA1 u hu v hv))))
                                                 bc (mul (p v) (c v)) mc (mul (Mu v) (c v))
                                                 zu (at 'z u) zv (at 'z v)
                                                 regroup (a/chain (T2 v)
                                                                  [(mul zu (mul (Mu u) bc)) (assoc3 zu (Mu u) bc)]
                                                                  [(mul zu (mul (Mu u) (mul zv mc)))
                                                                   (mcong zu zu (mul (Mu u) bc) (mul (Mu u) (mul zv mc)) (refl zu)
                                                                          (mcong (Mu u) (Mu u) bc (mul zv mc) (refl (Mu u)) (assoc3 zv (Mu v) (c v))))]
                                                                  [(mul zu (mul zv (K v)))
                                                                   (mcong zu zu (mul (Mu u) (mul zv mc)) (mul zv (K v)) (refl zu)
                                                                          (left-commute (Mu u) zv mc))])]
                                             (le-resp (mul zu (mul zv (K v))) (T2 v) (mul zu (K v)) (mul zu (K v))
                                                      (sym (T2 v) (mul zu (mul zv (K v))) regroup) (refl (mul zu (K v)))
                                                      (lmono zu (mul zv (K v)) (K v) hzu
                                                             (le-resp (mul zv (K v)) (mul zv (K v)) (mul one (K v)) (K v)
                                                                      (refl (mul zv (K v))) (one-times (K v))
                                                                      (rmono (K v) zv one hK (at 'hz1 v hv))))))))
                             (le-resp (mul (at 'z u) (sum KS 'n)) (sum G2 'n) (mul (at 'z u) s/zero) s/zero
                                      (call 'signed/expr-sum-value-scale-left KS (at 'z u) 'n) (call 'signed/multiply-zero-right (at 'z u))
                                      (lmono (at 'z u) (sum KS 'n) s/zero hzu (at 'hcl u hu))))
                mz (mul (Mu u) (at 'z u))]
            (le-resp (add (sum F1 'n) (sum F2 'n)) (sum FP 'n) (add mz s/zero) (p u)
                     (sym (sum FP 'n) (add (sum F1 'n) (sum F2 'n)) split)
                     (a/chain (add mz s/zero) [mz (call 'signed/add-zero-right mz)] [(p u) (comm (Mu u) (at 'z u))])
                     (le-trans (add (sum F1 'n) (sum F2 'n)) (add mz (sum F2 'n)) (add mz s/zero)
                               (call 'signed/add-right-monotone (sum F1 'n) mz (sum F2 'n) b1)
                               (call 'signed/add-left-monotone (sum F2 'n) s/zero mz b2)))))
        PS (f/lam [['ps nat]] (p 'ps))
        row (fn [u] (f/lam [['rw nat]] (mul (p u) (p 'rw))))
        rows (f/lam [['ru nat]] (sum (row 'ru) 'n))
        rescaled (f/lam [['sc nat]] (mul (p 'sc) S))
        square (a/chain (mul S S)
                        [(sum rescaled 'n) (call 'signed/expr-sum-value-scale-right PS S 'n)]
                        [(sum rows 'n) (a/sum-cong rescaled rows 'n 'qu
                                                   (fn [u _] (call 'signed/expr-sum-value-scale-left PS (p u) 'n)))])
        bounded (le-resp (sum rows 'n) (mul S S) S S (sym (mul S S) (sum rows 'n) square) (refl S)
                         (a/sum-mono rows PS 'n 'pu per-u))
        nonneg (call 'signed/expr-sum-value-nonnegative PS 'n
                     (f/lam [['nv nat] ['nv-lt (below 'nv 'n)]]
                            (nonneg-prod (at 'z 'nv) (at 'M 'C 'nv) (at 'hz0 'nv 'nv-lt) (at 'hM0 'nv 'nv-lt))))]
    (s/spec 'signed/independent-meets-clique-at-most-once
            [['A matrix] ['M matrix] ['z family] ['n nat] ['C nat]
             ['hz0 z-lo] ['hz1 z-hi] ['hM0 m-lo] ['hM1 m-hi]
             ['hA0 (all2 'au 'n 'av 'n #(le s/zero (at 'A %1 %2)))] ['hA1 (all2 'au 'n 'av 'n #(le (at 'A %1 %2) one))]
             ['hcl (clique-rows 'A 'M 'C 'n)] ['hind (indep-rows 'A 'z 'n)]]
            (le S one)
            (call 'signed/square-at-most-self-at-most-one S nonneg bounded))))

(defn cover [y M m v] (sum (f/lam [['dc nat]] (mul (at y 'dc) (at M 'dc v))) m))

(defn weight [w z n] (sum (f/lam [['dv nat]] (mul (at w 'dv) (at z 'dv))) n))

(defn total [y m] (sum (f/lam [['dy nat]] (at y 'dy)) m))

(defn duality-binders [A M w z y n m]
  (let [[z-lo z-hi] (unit-interval z n)]
    [['hz0 z-lo] ['hz1 z-hi]
     ['hA0 (all2 'au n 'av n #(le s/zero (at A %1 %2)))] ['hA1 (all2 'au n 'av n #(le (at A %1 %2) one))]
     ['hM0 (all2 'mc m 'mv n #(le s/zero (at M %1 %2)))] ['hM1 (all2 'mc m 'mv n #(le (at M %1 %2) one))]
     ['hcl (f/forall [['lc nat] ['lc-lt (below 'lc m)]] (clique-rows A M 'lc n))]
     ['hind (indep-rows A z n)]
     ['hy0 (s/all-below m #(le s/zero (at y %)))]
     ['hcov (s/all-below n #(le (at w %) (cover y M m %)))]]))

(def duality-spec
  (let [L1 (f/lam [['l1 nat]] (mul (at 'w 'l1) (at 'z 'l1)))
        L2 (f/lam [['l2 nat]] (mul (cover 'y 'M 'm 'l2) (at 'z 'l2)))
        cell (fn [v C] (mul (mul (at 'y C) (at 'M C v)) (at 'z v)))
        F (f/lam [['ev nat] ['ec nat]] (cell 'ev 'ec))
        by-vertex (f/lam [['bv nat]] (sum (f/lam [['bc nat]] (cell 'bv 'bc)) 'm))
        by-clique (f/lam [['xc nat]] (sum (f/lam [['xv nat]] (cell 'xv 'xc)) 'n))
        Y (f/lam [['dy nat]] (at 'y 'dy))
        per-clique
        (fn [C hC]
          (let [P (f/lam [['pv nat]] (mul (at 'z 'pv) (at 'M C 'pv)))
                Q (f/lam [['qv nat]] (mul (at 'y C) (mul (at 'z 'qv) (at 'M C 'qv))))
                SC (sum P 'n)
                count (call 'signed/independent-meets-clique-at-most-once 'A 'M 'z 'n C 'hz0 'hz1
                            (f/lam [['cv nat] ['cv-lt (below 'cv 'n)]] (at 'hM0 C hC 'cv 'cv-lt))
                            (f/lam [['cv nat] ['cv-lt (below 'cv 'n)]] (at 'hM1 C hC 'cv 'cv-lt))
                            'hA0 'hA1 (at 'hcl C hC) 'hind)]
            (le-resp (mul (at 'y C) SC) (sum (f/lam [['xv nat]] (cell 'xv C)) 'n) (mul (at 'y C) one) (at 'y C)
                     (a/chain (mul (at 'y C) SC)
                              [(sum Q 'n) (call 'signed/expr-sum-value-scale-left P (at 'y C) 'n)]
                              [(sum (f/lam [['xv nat]] (cell 'xv C)) 'n)
                               (a/sum-cong Q (f/lam [['xv nat]] (cell 'xv C)) 'n 'rv
                                           (fn [v _] (let [yc (at 'y C) zv (at 'z v) mcv (at 'M C v)]
                                                                (a/chain (mul yc (mul zv mcv))
                                                                         [(mul yc (mul mcv zv)) (mcong yc yc (mul zv mcv) (mul mcv zv) (refl yc) (comm zv mcv))]
                                                                         [(cell v C) (sym (cell v C) (mul yc (mul mcv zv)) (assoc3 yc mcv zv))]))))])
                     (times-one (at 'y C))
                     (lmono (at 'y C) SC one (at 'hy0 C hC) count))))]
    (s/spec 'signed/clique-cover-weak-duality
            (into [['A matrix] ['M matrix] ['w family] ['z family] ['y family] ['n nat] ['m nat]]
                  (duality-binders 'A 'M 'w 'z 'y 'n 'm))
            (le (weight 'w 'z 'n) (total 'y 'm))
            (le-trans (sum L1 'n) (sum L2 'n) (sum Y 'm)
                      (a/sum-mono L1 L2 'n 'wv
                                  (fn [v hv] (rmono (at 'z v) (at 'w v) (cover 'y 'M 'm v) (at 'hz0 v hv) (at 'hcov v hv))))
                      (le-resp (sum by-clique 'm) (sum L2 'n) (sum Y 'm) (sum Y 'm)
                               (a/chain (sum by-clique 'm)
                                        [(sum by-vertex 'n) (sym (sum by-vertex 'n) (sum by-clique 'm)
                                                                 (call 'signed/expr-sum-value-swap F 'm 'n))]
                                        [(sum L2 'n) (sym (sum L2 'n) (sum by-vertex 'n)
                                                          (a/sum-cong L2 by-vertex 'n 'cv
                                                                      (fn [v _] (call 'signed/expr-sum-value-scale-right
                                                                                      (f/lam [['sc nat]] (mul (at 'y 'sc) (at 'M 'sc v)))
                                                                                      (at 'z v) 'm))))])
                               (refl (sum Y 'm))
                               (a/sum-mono by-clique Y 'm 'yc per-clique))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn cell-index [cols row col] (call 'algebra/nat-add col (call 'nat/multiply row cols)))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec])

(def theorem-specs [total-spec one-minus-spec zero-one-upper-spec subtract-expand-spec square-bound-spec split-at-spec counting-spec duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      pairs/extend-environment
      positivity/extend-environment
      decide/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      multiply-associative/extend-environment
      multiply-ring/extend-environment
      limit-uniqueness/extend-environment
      (support/extend-with :expr-sum-indep-set-dual theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
