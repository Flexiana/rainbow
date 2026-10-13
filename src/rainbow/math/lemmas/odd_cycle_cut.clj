(ns rainbow.math.lemmas.odd-cycle-cut
  "General lemmas: odd cycle cut. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.lemmas.ncyc-infeasible :as ncyc]
            [rainbow.math.lemmas.bottleneck-assignment :as bottleneck]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.nat.pigeonhole :as pigeonhole]
            [rainbow.math.rational.signed.one-hot-selects :as one-hot-selects]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn nadd [x y] (call 'algebra/nat-add x y))

(defn nmul [x y] (call 'nat/multiply x y))

(defn eqn [x y] (f/equality type-level nat x y))

(defn nsym [x y h] (f/app (f/const* 'equality/symmetric [type-level]) nat x y h))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn witness [P w pf] (f/app (f/const* 'proposition/witness [type-level]) nat P w pf))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn both [p q] (call 'proposition/conjunction p q))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn bin [x] (disj (eqv x s/zero) (eqv x one)))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn one-of [y h]   ; 1 - y ~ 0  ->  y ~ 1
  (a/chain y [(sub one (sub one y)) (ring y (sub one (sub one y)))]
           [(sub one s/zero) (s/add-cong one one (neg (sub one y)) (neg s/zero) (refl one) (a/neg-cong (sub one y) s/zero h))]
           [one (ring (sub one s/zero) one)]))

(defn zo-disj [x h]  ; x (1 - x) ~ 0  ->  x ~ 0 \/ x ~ 1
  (cases (eqv x s/zero) (eqv (sub one x) s/zero) (bin x) (call 'signed/multiply-zero-split x (sub one x) h)
         (f/lam [['zd-z (eqv x s/zero)]] (call 'proposition/left-disjunct (eqv x s/zero) (eqv x one) 'zd-z))
         (f/lam [['zd-o (eqv (sub one x) s/zero)]] (call 'proposition/right-disjunct (eqv x s/zero) (eqv x one) (one-of x 'zd-o)))))

(def ofn of-nat/of-nat)

(defn ofn-nonneg [x] (call 'signed/zero-at-most-of-nonnegative (ofn x) (call 'nnrat/zero-at-most (of-nat/make x))))

(def two-nat (s/succ (s/succ s/nz)))

(defn L-of [k] (s/succ (nmul two-nat k)))

(def of-nat-add-spec
  (let [b 'oa-b claim (fn [x] (eqv (ofn (nadd x b)) (add (ofn x) (ofn b))))]
    (s/spec 'signed/of-nat-add [['oa-a nat] ['oa-b nat]]
            (claim 'oa-a)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['oa-x nat]] (claim 'oa-x))
                   (ring (ofn b) (add s/zero (ofn b)))
                   (f/lam [['oa-j nat] ['oa-ih (claim 'oa-j)]]
                          (let [j 'oa-j Oj (ofn j) Ob (ofn b) Ojb (ofn (nadd j b))]
                            (a/chain (ofn (nadd (s/succ j) b))
                                     [(add Ojb one) (call 'signed/of-nat-successor (nadd j b))]
                                     [(add (add Oj Ob) one) (s/add-cong Ojb (add Oj Ob) one one 'oa-ih (refl one))]
                                     [(add (add Oj one) Ob) (ring (add (add Oj Ob) one) (add (add Oj one) Ob))]
                                     [(add (ofn (s/succ j)) Ob) (s/add-cong (add Oj one) (ofn (s/succ j)) Ob Ob
                                                                            (sym (ofn (s/succ j)) (add Oj one) (call 'signed/of-nat-successor j)) (refl Ob))])))
                   'oa-a))))

(def of-nat-monotone-spec
  (let [a 'om-a b 'om-b goal (le (ofn a) (ofn b))]
    (s/spec 'signed/of-nat-monotone [['om-a nat] ['om-b nat] ['om-h (call 'nat/at-most a b)]]
            goal
            (f/app 'om-h goal
                   (f/lam [['om-e nat] ['om-he (eqn (nadd a 'om-e) b)]]
                          (subst-nat (nadd a 'om-e) b 'om-he (f/lam [['om-t nat]] (le (ofn a) (ofn 'om-t)))
                                     (le-resp (add (ofn a) s/zero) (ofn a) (add (ofn a) (ofn 'om-e)) (ofn (nadd a 'om-e))
                                              (call 'signed/add-zero-right (ofn a))
                                              (sym (ofn (nadd a 'om-e)) (add (ofn a) (ofn 'om-e)) (call 'signed/of-nat-add a 'om-e))
                                              (call 'signed/add-left-monotone s/zero (ofn 'om-e) (ofn a) (ofn-nonneg 'om-e)))))))))

(def of-nat-double-spec
  (let [k 'od-k Ok (ofn k)]
    (s/spec 'signed/of-nat-double [['od-k nat]]
            (eqv (ofn (nmul two-nat k)) (add Ok Ok))
            (a/chain (ofn (nadd k (nadd k s/nz)))
                     [(add Ok (ofn (nadd k s/nz))) (call 'signed/of-nat-add k (nadd k s/nz))]
                     [(add Ok (add Ok s/zero)) (s/add-cong Ok Ok (ofn (nadd k s/nz)) (add Ok s/zero) (refl Ok) (call 'signed/of-nat-add k s/nz))]
                     [(add Ok Ok) (ring (add Ok (add Ok s/zero)) (add Ok Ok))]))))

(def half-floor-spec
  (let [N 'hf-n k 'hf-k ON (ofn N) Ok (ofn k) X (add (add Ok Ok) one) goal (le ON Ok)]
    (s/spec 'signed/of-nat-half-floor [['hf-n nat] ['hf-k nat] ['hf-h (le (add ON ON) X)]]
            goal
            (cases (below N k) (disj (eqn N k) (below k N)) goal (call 'nat/trichotomy N k)
                   (f/lam [['hf-lt (below N k)]]
                          (le-trans ON (ofn (s/succ N)) Ok
                                    (call 'signed/of-nat-monotone N (s/succ N) (call 'nat/at-most-successor N))
                                    (call 'signed/of-nat-monotone (s/succ N) k 'hf-lt)))
                   (f/lam [['hf-rest (disj (eqn N k) (below k N))]]
                          (cases (eqn N k) (below k N) goal 'hf-rest
                                 (f/lam [['hf-eq (eqn N k)]]
                                        (subst-nat k N (nsym N k 'hf-eq) (f/lam [['hf-t nat]] (le (ofn 'hf-t) Ok)) (call 'signed/at-most-reflexive Ok)))
                                 (f/lam [['hf-gt (below k N)]]
                                        (let [A (add Ok one)
                                              hA (le-resp (ofn (s/succ k)) A ON ON (call 'signed/of-nat-successor k) (refl ON)
                                                          (call 'signed/of-nat-monotone (s/succ k) N 'hf-gt))
                                              AA (le-trans (add A A) (add ON A) (add ON ON)
                                                           (call 'signed/add-right-monotone A ON A hA)
                                                           (call 'signed/add-left-monotone A ON ON hA))
                                              bad (le-resp (add A A) (add X one) X X (ring (add A A) (add X one)) (refl X)
                                                           (le-trans (add A A) (add ON ON) X AA 'hf-h))]
                                          (call 'proposition/explode goal (call 'signed/not-successor-at-most-self X bad))))))))))

(defn is-count [T] (proposition/existence type-level nat (f/lam [['cnt nat]] (eqv T (ofn 'cnt)))))

(def zero-one-sum-spec
  (let [F 'zs-f claim (fn [m] (f/forall [['zs-h (s/all-below m #(bin (at F %)))]] (is-count (sum F m))))]
    (s/spec 'signed/zero-one-sum-of-nat [['zs-f family] ['zs-n nat]]
            (claim 'zs-n)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['zs-m nat]] (claim 'zs-m))
                   (f/lam [['zs-h (s/all-below s/nz #(bin (at F %)))]]
                          (witness (f/lam [['cnt nat]] (eqv (sum F s/nz) (ofn 'cnt))) s/nz (refl s/zero)))
                   (f/lam [['zs-j nat] ['zs-ih (claim 'zs-j)] ['zs-h (s/all-below (s/succ 'zs-j) #(bin (at F %)))]]
                          (let [j 'zs-j Sj (sum F j) Fj (at F j) goal (is-count (sum F (s/succ j)))
                                P1 (f/lam [['cnt nat]] (eqv (sum F (s/succ j)) (ofn 'cnt)))
                                weak (f/lam [['zs-i nat] ['zs-il (below 'zs-i j)]] (at 'zs-h 'zs-i (call 'nat/strict-below-weaken 'zs-i j 'zs-il)))]
                            (f/app (at 'zs-ih weak) goal
                                   (f/lam [['zs-c nat] ['zs-ce (eqv Sj (ofn 'zs-c))]]
                                          (let [C 'zs-c OC (ofn C)]
                                            (cases (eqv Fj s/zero) (eqv Fj one) goal (at 'zs-h j (s/self-below j))
                                                   (f/lam [['zs-z (eqv Fj s/zero)]]
                                                          (witness P1 C (a/chain (add Sj Fj)
                                                                                 [(add OC s/zero) (s/add-cong Sj OC Fj s/zero 'zs-ce 'zs-z)]
                                                                                 [OC (call 'signed/add-zero-right OC)])))
                                                   (f/lam [['zs-o (eqv Fj one)]]
                                                          (witness P1 (s/succ C) (a/chain (add Sj Fj)
                                                                                          [(add OC one) (s/add-cong Sj OC Fj one 'zs-ce 'zs-o)]
                                                                                          [(ofn (s/succ C)) (sym (ofn (s/succ C)) (add OC one) (call 'signed/of-nat-successor C))])))))))))
                   'zs-n))))

(def count-spec
  (let [z 'oc-z k 'oc-k L (L-of k) zt #(at z %) S (sum z L) K (ofn k) X (add (add K K) one)
        H (f/lam [['oc-t nat]] (add (zt 'oc-t) (zt (s/succ 'oc-t))))
        ONE (f/lam [['oc-u nat]] one)
        ZZ (f/lam [['oc-w nat]] (add (zt 'oc-w) (zt 'oc-w)))
        D (f/lam [['tq nat]] (sub (zt (s/succ 'tq)) (zt 'tq)))
        H2 (f/lam [['oc-v nat]] (add (at ZZ 'oc-v) (at D 'oc-v)))
        z0 (zt s/nz) zL (zt L)
        upper (a/chain (sum ONE L)
                       [(mul one (ofn L)) (call 'signed/expr-sum-constant-of-nat one L)]
                       [(ofn L) (one-times (ofn L))]
                       [(add (ofn (nmul two-nat k)) one) (call 'signed/of-nat-successor (nmul two-nat k))]
                       [X (s/add-cong (ofn (nmul two-nat k)) (add K K) one one (call 'signed/of-nat-double k) (refl one))])
        gap0 (a/chain (sub zL z0)
                      [(sub z0 z0) (s/add-cong zL z0 (neg z0) (neg z0) 'oc-close (refl (neg z0)))]
                      [s/zero (ring (sub z0 z0) s/zero)])
        lower (a/chain (sum H L)
                       [(sum H2 L) (a/sum-cong H H2 L 'oc-c (fn [t _] (ring (add (zt t) (zt (s/succ t))) (add (add (zt t) (zt t)) (sub (zt (s/succ t)) (zt t))))))]
                       [(add (sum ZZ L) (sum D L)) (call 'signed/expr-sum-value-add ZZ D L)]
                       [(add (add S S) (sub zL z0)) (s/add-cong (sum ZZ L) (add S S) (sum D L) (sub zL z0)
                                                                (call 'signed/expr-sum-value-add z z L) (call 'signed/expr-sum-value-telescope z L))]
                       [(add (add S S) s/zero) (s/add-cong (add S S) (add S S) (sub zL z0) s/zero (refl (add S S)) gap0)]
                       [(add S S) (call 'signed/add-zero-right (add S S))])
        twice (le-resp (sum H L) (add S S) (sum ONE L) X lower upper
                       (a/sum-mono H ONE L 'oc-m (fn [t ht] (at 'oc-adj t ht))))
        goal (le S K)]
    (s/spec 'signed/odd-cycle-count
            [['oc-z family] ['oc-k nat]
             ['oc-01 (s/all-below L #(bin (zt %)))]
             ['oc-adj (s/all-below L #(le (add (zt %) (zt (s/succ %))) one))]
             ['oc-close (eqv zL z0)]]
            goal
            (f/app (call 'signed/zero-one-sum-of-nat z L 'oc-01) goal
                   (f/lam [['oc-n nat] ['oc-ne (eqv S (ofn 'oc-n))]]
                          (let [N 'oc-n ON (ofn N)]
                            (le-resp ON S K K (sym S ON 'oc-ne) (refl K)
                                     (call 'signed/of-nat-half-floor N k
                                           (le-resp (add S S) (add ON ON) X X (s/add-cong S ON S ON 'oc-ne 'oc-ne) (refl X) twice)))))))))

(defn weighted [A y] (f/lam [['wi nat]] (mul (at A 'wi) (at y 'wi))))

(def step-spec
  (let [n 'st-n A 'st-a B 'st-b E 'st-e y 'st-y yv #(at y %)
        zA (sum (weighted A y) n) zB (sum (weighted B y) n)
        inner (fn [u] (sum (f/lam [['st-v nat]] (mul (at B 'st-v) (at E u 'st-v))) n))
        F (f/lam [['st-u nat]] (mul (at A 'st-u) (inner 'st-u)))
        stepsum (sum F n)
        goal (both (bin zA) (le (add zA zB) one))
        reads (fn [S p] (f/forall [['X family]] (eqv (sum (f/lam [['i nat]] (mul (at S 'i) (at 'X 'i))) n) (at 'X p))))
        tail (fn [S p] (both (eqv (at S p) one) (reads S p)))
        sel-prop (fn [S p] (both (below p n) (tail S p)))
        select (fn [S h01 hsum]
                 (call 'signed/one-hot-selects S n
                       (f/lam [['sn-i nat] ['sn-h (below 'sn-i n)]] (call 'signed/zero-one-nonnegative (at S 'sn-i) (at h01 'sn-i 'sn-h)))
                       (f/lam [['sd-i nat] ['sd-h (below 'sd-i n)]] (zo-disj (at S 'sd-i) (at h01 'sd-i 'sd-h)))
                       hsum))
        lt-of (fn [S p h] (call 'proposition/left (below p n) (tail S p) h))
        reads-of (fn [S p h] (call 'proposition/right (eqv (at S p) one) (reads S p) (call 'proposition/right (below p n) (tail S p) h)))]
    (s/spec 'signed/odd-cycle-step
            [['st-n nat] ['st-a family] ['st-b family] ['st-e matrix] ['st-y family]
             ['st-a01 (s/all-below n #(zero-one (at A %)))] ['st-asum (eqv (sum A n) one)]
             ['st-b01 (s/all-below n #(zero-one (at B %)))] ['st-bsum (eqv (sum B n) one)]
             ['st-step (eqv stepsum one)]
             ['st-y01 (s/all-below n #(zero-one (yv %)))]
             ['st-free (all2 'fu n 'fv n #(eqv (mul (mul (yv %1) (yv %2)) (at E %1 %2)) s/zero))]]
            goal
            (f/app (select A 'st-a01 'st-asum) goal
                   (f/lam [['st-p nat] ['st-ph (sel-prop A 'st-p)]]
                          (f/app (select B 'st-b01 'st-bsum) goal
                                 (f/lam [['st-q nat] ['st-qh (sel-prop B 'st-q)]]
                                        (let [p 'st-p q 'st-q yp (yv p) yq (yv q)
                                              pl (lt-of A p 'st-ph) pr (reads-of A p 'st-ph)
                                              ql (lt-of B q 'st-qh) qr (reads-of B q 'st-qh)
                                              zA-y (at pr y) zB-y (at qr y)
                                              G (f/lam [['st-g nat]] (mul (at A 'st-g) (at E 'st-g q)))
                                              s1 (a/sum-cong F G n 'st-c
                                                             (fn [u _] (mcong (at A u) (at A u) (inner u) (at E u q) (refl (at A u))
                                                                              (at qr (f/lam [['st-w nat]] (at E u 'st-w))))))
                                              s2 (at pr (f/lam [['st-x nat]] (at E 'st-x q)))
                                              Epq (at E p q)
                                              Epq-one (trans Epq stepsum one (sym stepsum Epq (trans stepsum (sum G n) Epq s1 s2)) 'st-step)
                                              yy0 (a/chain (mul yp yq)
                                                           [(mul (mul yp yq) one) (sym (mul (mul yp yq) one) (mul yp yq) (times-one (mul yp yq)))]
                                                           [(mul (mul yp yq) Epq) (mcong (mul yp yq) (mul yp yq) one Epq (refl (mul yp yq)) (sym Epq one Epq-one))]
                                                           [s/zero (at 'st-free p pl q ql)])]
                                          (cases (eqv yp s/zero) (eqv yp one) goal (zo-disj yp (at 'st-y01 p pl))
                                                 (f/lam [['st-yz (eqv yp s/zero)]]
                                                        (let [sum-y (a/chain (add zA zB)
                                                                             [(add s/zero yq) (s/add-cong zA s/zero zB yq (trans zA yp s/zero zA-y 'st-yz) zB-y)]
                                                                             [yq (ring (add s/zero yq) yq)])]
                                                          (call 'proposition/conjoin (bin zA) (le (add zA zB) one)
                                                                (call 'proposition/left-disjunct (eqv zA s/zero) (eqv zA one) (trans zA yp s/zero zA-y 'st-yz))
                                                                (le-resp yq (add zA zB) one one (sym (add zA zB) yq sum-y) (refl one)
                                                                         (call 'signed/zero-one-at-most-one yq (at 'st-y01 q ql))))))
                                                 (f/lam [['st-yo (eqv yp one)]]
                                                        (let [yq0 (a/chain yq
                                                                           [(mul one yq) (sym (mul one yq) yq (one-times yq))]
                                                                           [(mul yp yq) (mcong one yp yq yq (sym yp one 'st-yo) (refl yq))]
                                                                           [s/zero yy0])
                                                              sum-one (a/chain (add zA zB)
                                                                               [(add one s/zero) (s/add-cong zA one zB s/zero (trans zA yp one zA-y 'st-yo) (trans zB yq s/zero zB-y yq0))]
                                                                               [one (call 'signed/add-zero-right one)])]
                                                          (call 'proposition/conjoin (bin zA) (le (add zA zB) one)
                                                                (call 'proposition/right-disjunct (eqv zA s/zero) (eqv zA one) (trans zA yp one zA-y 'st-yo))
                                                                (a/eq-le (add zA zB) one sum-one)))))))))))))

(def bool (f/const* 'data/Bool []))

(def btrue (f/const* 'data/true []))

(defn sel [c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) one s/zero c))

(def separates-spec
  (let [T 'sp-t k 'sp-k K (ofn k) stwo (ofn two-nat) two-k (ofn (nmul two-nat k))
        D (call 'signed/decide-at-most (mul stwo T) two-k)
        two-eq (a/chain stwo
                        [(add (ofn (s/succ s/nz)) one) (call 'signed/of-nat-successor (s/succ s/nz))]
                        [(add (add s/zero one) one) (s/add-cong (ofn (s/succ s/nz)) (add s/zero one) one one (call 'signed/of-nat-successor s/nz) (refl one))]
                        [(add one one) (ring (add (add s/zero one) one) (add one one))])
        scaled (a/chain (mul stwo K)
                        [(mul K stwo) (call 'signed/multiply-commutative stwo K)]
                        [(mul K (add one one)) (mcong K K stwo (add one one) (refl K) two-eq)]
                        [(add (mul K one) (mul K one)) (call 'signed/multiply-distributes-add-left K one one)]
                        [(add K K) (s/add-cong (mul K one) K (mul K one) K (times-one K) (times-one K))]
                        [two-k (sym two-k (add K K) (call 'signed/of-nat-double k))])
        h2 (le-resp (mul stwo T) (mul stwo T) (mul stwo K) two-k (refl (mul stwo T)) scaled
                    (call 'signed/multiply-left-monotone stwo T K (ofn-nonneg two-nat) 'sp-le))
        dtrue (call 'signed/decide-at-most-true-complete (mul stwo T) two-k h2)
        v-true (f/app (f/const* 'equality/substitution [type-level]) bool D btrue dtrue (f/lam [['ct bool]] (le one (sel 'ct))) 'sp-v)]
    (s/spec 'signed/odd-cycle-separates [['sp-t signed] ['sp-k nat] ['sp-v (le one (sel D))] ['sp-le (le T K)]]
            (f/const* 'proposition/falsity [])
            (call 'signed/one-not-at-most-zero v-true))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec indep/zero-one-upper-spec indep/one-minus-spec indep/subtract-expand-spec
                     ncyc/telescope-spec bottleneck/no-successor-below-spec])

(def theorem-specs [of-nat-add-spec of-nat-monotone-spec of-nat-double-spec half-floor-spec zero-one-sum-spec count-spec step-spec separates-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.nat.pigeonhole rainbow.math.rational.signed.add-zero-reflection rainbow.math.rational.signed.one-hot-attained rainbow.math.rational.signed.one-hot-keep rainbow.math.rational.signed.order-cancellation rainbow.math.rational.signed.one-hot-selects])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-odd-cycle-cut borrowed-specs) (support/extend-with-shared :expr-sum-odd-cycle-cut theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.odd-cycle-cut))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
