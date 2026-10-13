(ns rainbow.math.lemmas.bottleneck-assignment
  "General lemmas: bottleneck assignment. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
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

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn eqb [x y] (f/equality type-level bool x y))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(defn all2 [p n q k body]
  (f/forall [[p nat] [(symbol (str p "-lt")) (below p n)] [q nat] [(symbol (str q "-lt")) (below q k)]] (body p q)))

(defn cheaper [b x] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) one s/zero (call 'signed/decide-at-most b x)))

(def cheaper-one-spec
  (let [D (call 'signed/decide-at-most 'b 'x)
        sel (fn [t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) one s/zero t))
        not-ba (f/lam [['hba (le 'b 'x)]] (at 'hnot (le-trans 'b 'x 'B 'hba 'hxB)))
        dfalse (call 'signed/decide-at-most-false-complete 'b 'x not-ba)]
    (s/spec 'signed/cheaper-indicator-one
            [['b signed] ['x signed] ['B signed] ['hxB (le 'x 'B)] ['hnot (f/arrow (le 'b 'B) (f/const* 'proposition/falsity []))]]
            (eqv (sel D) one)
            (f/app (f/const* 'equality/substitution [type-level]) bool bfalse D
                   (f/app (f/const* 'equality/symmetric [type-level]) bool D bfalse dfalse)
                   (f/lam [['ct bool]] (eqv (sel 'ct) one))
                   (refl one)))))

(def no-successor-below-spec
  (s/spec 'signed/not-successor-at-most-self [['X signed] ['h (le (add 'X one) 'X)]]
          (f/const* 'proposition/falsity [])
          (call 'signed/one-not-at-most-zero
                (le-resp (add (add 'X one) (neg 'X)) one (add 'X (neg 'X)) s/zero
                         (ring (add (add 'X one) (neg 'X)) one) (ring (add 'X (neg 'X)) s/zero)
                         (call 'signed/add-right-monotone (add 'X one) 'X (neg 'X) 'h)))))

(defn row-sum [y n i] (sum (f/lam [['rj nat]] (at y i 'rj)) n))

(defn col-sum [y n j] (sum (f/lam [['ci nat]] (at y 'ci j)) n))

(defn permutation-binders [y n]
  [['hy01 (all2 'yi n 'yj n #(zero-one (at y %1 %2)))]
   ['hrow (s/all-below n #(eqv (row-sum y n %) one))]
   ['hcol (s/all-below n #(eqv (col-sum y n %) one))]])

(defn bottleneck-premise [y A B n] ['hbot (all2 'bi n 'bj n #(le (mul (at y %1 %2) (sub (at A %1 %2) B)) s/zero))])

(def lower-spec
  (let [A 'A r 'r c 'c b 'b B 'B n 'n y 'y
        SR (sum (f/lam [['sr nat]] (at r 'sr)) n) SC (sum (f/lam [['sc nat]] (at c 'sc)) n)
        D (call 'signed/decide-at-most b B)
        goal (fn [_] (le b B))
        ;; when b <= B fails: each cell, y <= y (r_i + c_j)
        cell (fn [hnot i j hi hj]
               (let [yv (at y i j) rc (add (at r i) (at c j)) goal (le yv (mul yv rc))]
                 (cases (eqv yv s/zero) (eqv (sub one yv) s/zero) goal (call 'signed/multiply-zero-split yv (sub one yv) (at 'hy01 i hi j hj))
                        (f/lam [['yz (eqv yv s/zero)]]
                               (a/eq-le yv (mul yv rc)
                                        (a/chain yv [s/zero 'yz] [(mul s/zero rc) (sym (mul s/zero rc) s/zero (call 'signed/multiply-zero-left rc))]
                                                 [(mul yv rc) (mcong s/zero yv rc rc (sym yv s/zero 'yz) (refl rc))])))
                        (f/lam [['yo (eqv (sub one yv) s/zero)]]
                               (let [y1 (a/chain yv [(sub one (sub one yv)) (ring yv (sub one (sub one yv)))]
                                                 [(sub one s/zero) (s/add-cong one one (neg (sub one yv)) (neg s/zero) (refl one) (a/neg-cong (sub one yv) s/zero 'yo))]
                                                 [one (ring (sub one s/zero) one)])
                                     ax (at A i j)
                                     dif (le-resp (mul yv (sub ax B)) (sub ax B) s/zero s/zero
                                                  (trans (mul yv (sub ax B)) (mul one (sub ax B)) (sub ax B) (mcong yv one (sub ax B) (sub ax B) y1 (refl (sub ax B))) (one-times (sub ax B)))
                                                  (refl s/zero) (at 'hbot i hi j hj))
                                     axB (le-resp (add (sub ax B) B) ax (add s/zero B) B (ring (add (sub ax B) B) ax) (ring (add s/zero B) B)
                                                  (call 'signed/add-right-monotone (sub ax B) s/zero B dif))
                                     ind1 (call 'signed/cheaper-indicator-one b ax B axB hnot)
                                     one-rc (le-resp (cheaper b ax) one rc rc ind1 (refl rc) (at 'hcov i hi j hj))
                                     y0 (le-resp s/zero s/zero one yv (refl s/zero) (sym yv one y1)
                                                 (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))]
                                 (le-resp (mul yv one) yv (mul yv rc) (mul yv rc) (times-one yv) (refl (mul yv rc))
                                          (lmono yv one rc y0 one-rc)))))))
        Yrow (f/lam [['yr nat]] (row-sum y n 'yr))
        YRC (f/lam [['ya nat]] (sum (f/lam [['yb nat]] (mul (at y 'ya 'yb) (add (at r 'ya) (at c 'yb)))) n))
        P1 (fn [i] (f/lam [['p1 nat]] (mul (at y i 'p1) (at r i))))
        P2 (fn [i] (f/lam [['p2 nat]] (mul (at y i 'p2) (at c 'p2))))
        ;; sum_i sum_j y_ij ~ of-nat n
        total-y (a/chain (sum Yrow n)
                         [(sum (f/lam [['yo nat]] one) n) (a/sum-cong Yrow (f/lam [['yo nat]] one) n 'ta (fn [i hi] (at 'hrow i hi)))]
                         [(mul one (of-nat/of-nat n)) (call 'signed/expr-sum-constant-of-nat one n)]
                         [(of-nat/of-nat n) (one-times (of-nat/of-nat n))])
        ;; sum_i sum_j y_ij (r_i + c_j) ~ sum r + sum c
        first-part (a/chain (sum (f/lam [['f1 nat]] (sum (P1 'f1) n)) n)
                            [(sum (f/lam [['f2 nat]] (mul (row-sum y n 'f2) (at r 'f2))) n)
                             (a/sum-cong (f/lam [['f1 nat]] (sum (P1 'f1) n)) (f/lam [['f2 nat]] (mul (row-sum y n 'f2) (at r 'f2))) n 'fa
                                         (fn [i _] (sym (mul (row-sum y n i) (at r i)) (sum (P1 i) n) (call 'signed/expr-sum-value-scale-right (f/lam [['rj nat]] (at y i 'rj)) (at r i) n))))]
                            [SR (a/sum-cong (f/lam [['f2 nat]] (mul (row-sum y n 'f2) (at r 'f2))) (f/lam [['sr nat]] (at r 'sr)) n 'fb
                                            (fn [i hi] (trans (mul (row-sum y n i) (at r i)) (mul one (at r i)) (at r i)
                                                              (mcong (row-sum y n i) one (at r i) (at r i) (at 'hrow i hi) (refl (at r i))) (one-times (at r i)))))])
        T2 (f/lam [['t2i nat] ['t2j nat]] (mul (at y 't2i 't2j) (at c 't2j)))
        second-part (a/chain (sum (f/lam [['s1 nat]] (sum (P2 's1) n)) n)
                             [(sum (f/lam [['s2 nat]] (sum (f/lam [['s3 nat]] (mul (at y 's3 's2) (at c 's2))) n)) n) (call 'signed/expr-sum-value-swap T2 n n)]
                             [(sum (f/lam [['s4 nat]] (mul (col-sum y n 's4) (at c 's4))) n)
                              (a/sum-cong (f/lam [['s2 nat]] (sum (f/lam [['s3 nat]] (mul (at y 's3 's2) (at c 's2))) n)) (f/lam [['s4 nat]] (mul (col-sum y n 's4) (at c 's4))) n 'sa
                                          (fn [j _] (sym (mul (col-sum y n j) (at c j)) (sum (f/lam [['s3 nat]] (mul (at y 's3 j) (at c j))) n)
                                                         (call 'signed/expr-sum-value-scale-right (f/lam [['ci nat]] (at y 'ci j)) (at c j) n))))]
                             [SC (a/sum-cong (f/lam [['s4 nat]] (mul (col-sum y n 's4) (at c 's4))) (f/lam [['sc nat]] (at c 'sc)) n 'sb
                                             (fn [j hj] (trans (mul (col-sum y n j) (at c j)) (mul one (at c j)) (at c j)
                                                               (mcong (col-sum y n j) one (at c j) (at c j) (at 'hcol j hj) (refl (at c j))) (one-times (at c j)))))])
        total-rc (a/chain (sum YRC n)
                          [(sum (f/lam [['u1 nat]] (add (sum (P1 'u1) n) (sum (P2 'u1) n))) n)
                           (a/sum-cong YRC (f/lam [['u1 nat]] (add (sum (P1 'u1) n) (sum (P2 'u1) n))) n 'ua
                                       (fn [i _] (a/chain (sum (f/lam [['yb nat]] (mul (at y i 'yb) (add (at r i) (at c 'yb)))) n)
                                                          [(sum (f/lam [['u2 nat]] (add (at (P1 i) 'u2) (at (P2 i) 'u2))) n)
                                                           (a/sum-cong (f/lam [['yb nat]] (mul (at y i 'yb) (add (at r i) (at c 'yb)))) (f/lam [['u2 nat]] (add (at (P1 i) 'u2) (at (P2 i) 'u2))) n 'ub
                                                                       (fn [j _] (call 'signed/multiply-distributes-add-left (at y i j) (at r i) (at c j))))]
                                                          [(add (sum (P1 i) n) (sum (P2 i) n)) (call 'signed/expr-sum-value-add (P1 i) (P2 i) n)])))]
                          [(add (sum (f/lam [['f1 nat]] (sum (P1 'f1) n)) n) (sum (f/lam [['s1 nat]] (sum (P2 's1) n)) n))
                           (call 'signed/expr-sum-value-add (f/lam [['f1 nat]] (sum (P1 'f1) n)) (f/lam [['s1 nat]] (sum (P2 's1) n)) n)]
                          [(add SR SC) (s/add-cong (sum (f/lam [['f1 nat]] (sum (P1 'f1) n)) n) SR (sum (f/lam [['s1 nat]] (sum (P2 's1) n)) n) SC first-part second-part)])
        contradiction (fn [hnot]
                        (let [n-le (le-resp (sum Yrow n) (of-nat/of-nat n) (sum YRC n) (add SR SC) total-y total-rc
                                            (a/sum-mono Yrow YRC n 'ma
                                                        (fn [i hi] (a/sum-mono (f/lam [['rj nat]] (at y i 'rj)) (f/lam [['yb nat]] (mul (at y i 'yb) (add (at r i) (at c 'yb)))) n 'mb
                                                                               (fn [j hj] (cell hnot i j hi hj))))))]
                          (call 'signed/not-successor-at-most-self (add SR SC)
                                (le-trans (add (add SR SC) one) (of-nat/of-nat n) (add SR SC) 'hsize n-le))))]
    (s/spec 'signed/bottleneck-assignment-lower-bound
            (-> [['A matrix] ['r family] ['c family] ['b signed] ['n nat]
                 ['hcov (all2 'ki n 'kj n #(le (cheaper b (at A %1 %2)) (add (at r %1) (at c %2))))]
                 ['hsize (le (add (add SR SC) one) (of-nat/of-nat n))]
                 ['y matrix] ['B signed]]
                (into (permutation-binders y n)) (conj (bottleneck-premise y A B n)))
            (le b B)
            (f/app (f/const* 'data/Bool.rec [prop-level])
                   (f/lam [['db bool]] (f/forall [['dh (eqb D 'db)]] (le b B)))
                   (f/lam [['dh (eqb D bfalse)]]
                          (call 'proposition/explode (le b B) (contradiction (call 'signed/decide-at-most-false-sound b B 'dh))))
                   (f/lam [['dh (eqb D btrue)]] (call 'signed/decide-at-most-true-sound b B 'dh))
                   D
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D)))))

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

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec])

(def theorem-specs [cheaper-one-spec no-successor-below-spec lower-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      dot-negate/extend-environment
      of-nat/extend-environment
      pairs/extend-environment
      (support/extend-with-shared :expr-sum-bottleneck-assignment theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
