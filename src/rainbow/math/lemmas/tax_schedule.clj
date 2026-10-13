(ns rainbow.math.lemmas.tax-schedule
  "General lemmas: tax schedule. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.nat.strict-below-more :as nat-more]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn lt [x y] (call 'signed/less-than x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn le-refl [x] (call 'signed/at-most-reflexive x))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn explode [p h] (call 'proposition/explode p h))

(defn eqn [x y] (f/equality type-level nat x y))

(defn add-le [a b c d hab hcd]   ; a <= b, c <= d -> a + c <= b + d
  (le-trans (add a c) (add b c) (add b d) (call 'signed/add-right-monotone a b c hab) (call 'signed/add-left-monotone c d b hcd)))

(defn sel [f-branch t-branch c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) f-branch t-branch c))

(defn clamp [g w] (sel (sel w g (call 'signed/decide-at-most g w)) s/zero (call 'signed/decide-at-most g s/zero)))

(defn clamp-facts [t g w]
  (pconj (le s/zero t) (pconj (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g))))))

(def clamp-spec
  (let [g 'cl-g w 'cl-w D1 (call 'signed/decide-at-most g s/zero) D2 (call 'signed/decide-at-most g w)
        eqb (fn [D t] (f/equality type-level bool D t))
        fT (f/const* 'data/false []) tT (f/const* 'data/true [])
        inner (fn [b2] (sel w g b2))
        outer (fn [b1 in] (sel in s/zero b1))
        facts (fn [t] (clamp-facts t g w))
        ;; facts for a fixed value, built from its four parts
        mk (fn [t p1 p2 p3 p4] (conjoin (le s/zero t) (pconj (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g))))
                                        p1 (conjoin (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)))
                                                    p2 (conjoin (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)) p3 p4))))
        claim1 (fn [b1] (f/forall [['cl-e1 (eqb D1 b1)]] (facts (outer b1 (inner D2)))))
        claim2 (fn [b2] (f/forall [['cl-e2 (eqb D2 b2)]] (facts (inner b2))))
        ;; decided true at the outer bit: t = 0
        zero-case (mk s/zero (le-refl s/zero) 'cl-hw
                      (f/lam [['cl-a (le g s/zero)]] (refl s/zero))
                      (f/lam [['cl-b (le s/zero g)]] 'cl-b))
        ;; decided false at the outer bit: not (g <= 0), so 0 <= g
        not-le0 (fn [e1] (call 'signed/decide-at-most-false-sound g s/zero e1))
        pos-g (fn [e1] (cases (le g s/zero) (le s/zero g) (le s/zero g) (call 'signed/at-most-total g s/zero)
                              (f/lam [['cl-x (le g s/zero)]] (explode (le s/zero g) (f/app (not-le0 e1) 'cl-x)))
                              (f/lam [['cl-y (le s/zero g)]] 'cl-y)))
        inner-proof (fn [e1]
                      (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                                    (f/lam [['cl-b2 bool]] (claim2 'cl-b2))
                                    ;; g <= w decided false: t = w, w <= g
                                    (f/lam [['cl-e2 (eqb D2 fT)]]
                                           (let [w-le-g (cases (le g w) (le w g) (le w g) (call 'signed/at-most-total g w)
                                                               (f/lam [['cl-p (le g w)]] (explode (le w g) (f/app (call 'signed/decide-at-most-false-sound g w 'cl-e2) 'cl-p)))
                                                               (f/lam [['cl-q (le w g)]] 'cl-q))]
                                             (mk w 'cl-hw (le-refl w)
                                                 (f/lam [['cl-a (le g s/zero)]] (explode (eqv w s/zero) (f/app (not-le0 e1) 'cl-a)))
                                                 (f/lam [['cl-b (le s/zero g)]] w-le-g))))
                                    ;; g <= w decided true: t = g
                                    (f/lam [['cl-e2 (eqb D2 tT)]]
                                           (mk g (pos-g e1) (call 'signed/decide-at-most-true-sound g w 'cl-e2)
                                               (f/lam [['cl-a (le g s/zero)]] (explode (eqv g s/zero) (f/app (not-le0 e1) 'cl-a)))
                                               (f/lam [['cl-b (le s/zero g)]] (le-refl g))))
                                    D2)
                             (f/app (f/const* 'equality/reflexive [type-level]) bool D2)))]
    (s/spec 'signed/tax-clamp [['cl-g signed] ['cl-w signed] ['cl-hw (le s/zero w)]]
            (facts (clamp g w))
            (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                          (f/lam [['cl-b1 bool]] (claim1 'cl-b1))
                          (f/lam [['cl-e1 (eqb D1 fT)]] (inner-proof 'cl-e1))
                          (f/lam [['cl-e1 (eqb D1 tT)]] zero-case)
                          D1)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool D1)))))

(def step-spec
  (let [[S t b w y] '[fs-s fs-t fs-b fs-w fs-y] g (sub y b) goal (pconj (le (add S t) y) (le (add S t) (add b w)))
        A (pleft (le s/zero t) (pconj (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)))) 'fs-cf)
        r1 (pright (le s/zero t) (pconj (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)))) 'fs-cf)
        B (pleft (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g))) r1)
        r2 (pright (le t w) (pconj (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g))) r1)
        C (pleft (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)) r2)
        Dd (pright (f/arrow (le g s/zero) (eqv t s/zero)) (f/arrow (le s/zero g) (le t g)) r2)
        St-le-bw (add-le S b t w 'fs-sb B)]
    (s/spec 'signed/tax-fill-step
            [['fs-s signed] ['fs-t signed] ['fs-b signed] ['fs-w signed] ['fs-y signed]
             ['fs-sy (le S y)] ['fs-sb (le S b)] ['fs-cf (clamp-facts t g w)]]
            goal
            (cases (le g s/zero) (le s/zero g) goal (call 'signed/at-most-total g s/zero)
                   (f/lam [['fs-n (le g s/zero)]]
                          (let [t0 (f/app C 'fs-n)
                                St-S (a/chain (add S t) [(add S s/zero) (s/add-cong S S t s/zero (refl S) t0)] [S (call 'signed/add-zero-right S)])]
                            (conjoin (le (add S t) y) (le (add S t) (add b w))
                                     (le-resp S (add S t) y y (sym (add S t) S St-S) (refl y) 'fs-sy)
                                     St-le-bw)))
                   (f/lam [['fs-p (le s/zero g)]]
                          (conjoin (le (add S t) y) (le (add S t) (add b w))
                                   (le-resp (add S t) (add S t) (add b g) y (refl (add S t)) (ring (add b g) y)
                                            (add-le S b t g 'fs-sb (f/app Dd 'fs-p)))
                                   St-le-bw))))))

(defn psum [t m] (sum t m))

(def fill-spec
  (let [[t b w y q] '[fl-t fl-b fl-w fl-y fl-q] K (s/succ q)
        g (fn [k] (sub y (at b k)))
        claim (fn [m] (f/forall [['fl-hm (below m K)]] (pconj (le (psum t m) y) (le (psum t m) (at b m)))))
        cf (fn [k hk] (at 'fl-cf k hk))
        step (fn [m hm prev]
               (call 'signed/tax-fill-step (psum t m) (at t m) (at b m) (at w m) y
                     (pleft (le (psum t m) y) (le (psum t m) (at b m)) prev)
                     (pright (le (psum t m) y) (le (psum t m) (at b m)) prev)
                     (cf m hm)))
        base (f/lam [['fl-hm (below s/nz K)]]
                    (conjoin (le s/zero y) (le s/zero (at b s/nz)) 'fl-hy (a/eq-le s/zero (at b s/nz) (sym (at b s/nz) s/zero 'fl-b0))))
        ind (f/lam [['fl-j nat] ['fl-ih (claim 'fl-j)] ['fl-hm (below (s/succ 'fl-j) K)]]
                   (let [j 'fl-j
                         hj (call 'nat/at-most-transitive (s/succ j) (s/succ (s/succ j)) K (call 'nat/at-most-successor (s/succ j)) 'fl-hm)
                         jq (call 'nat/at-most-of-successor-at-most (s/succ j) q 'fl-hm)
                         st (step j hj (at 'fl-ih hj))
                         bw (add (at b j) (at w j))]
                     (conjoin (le (psum t (s/succ j)) y) (le (psum t (s/succ j)) (at b (s/succ j)))
                              (pleft (le (add (psum t j) (at t j)) y) (le (add (psum t j) (at t j)) bw) st)
                              (le-resp (add (psum t j) (at t j)) (add (psum t j) (at t j)) bw (at b (s/succ j)) (refl (add (psum t j) (at t j)))
                                       (sym (at b (s/succ j)) bw (at 'fl-bs j jq))
                                       (pright (le (add (psum t j) (at t j)) y) (le (add (psum t j) (at t j)) bw) st)))))
        all (f/app (f/const* 'data/Nat.rec [prop-level]) (f/lam [['fl-k nat]] (claim 'fl-k)) base ind q)
        last (step q (s/self-below q) (at all (s/self-below q)))]
    (s/spec 'signed/tax-fill
            [['fl-t family] ['fl-b family] ['fl-w family] ['fl-y signed] ['fl-q nat]
             ['fl-cf (s/all-below K #(clamp-facts (at t %) (g %) (at w %)))]
             ['fl-b0 (eqv (at b s/nz) s/zero)]
             ['fl-bs (s/all-below q #(eqv (at b (s/succ %)) (add (at b %) (at w %))))]
             ['fl-hy (le s/zero y)]]
            (le (psum t K) y)
            (pleft (le (add (psum t q) (at t q)) y) (le (add (psum t q) (at t q)) (add (at b q) (at w q))) last))))

(def prefix-spec
  (let [r 'rp-r q 'rp-q K (s/succ q)
        claim (fn [m] (f/forall [['rp-hm (below m K)] ['rp-k nat] ['rp-hk (below 'rp-k (s/succ m))]] (le (at r 'rp-k) (at r m))))
        base (f/lam [['rp-hm (below s/nz K)] ['rp-k nat] ['rp-hk (below 'rp-k (s/succ s/nz))]]
                    (two-terms/split-last 'rp-k 'rp-hk s/nz (le (at r 'rp-k) (at r s/nz))
                                          (f/lam [['rp-e (eqn 'rp-k s/nz)]]
                                                 (f/app (f/const* 'equality/substitution [type-level]) nat s/nz 'rp-k
                                                        (f/app (f/const* 'equality/symmetric [type-level]) nat 'rp-k s/nz 'rp-e)
                                                        (f/lam [['rp-z nat]] (le (at r 'rp-z) (at r s/nz))) (le-refl (at r s/nz))))
                                          (f/lam [['rp-l (below 'rp-k s/nz)]] (two-terms/impossible-bound 'rp-k 'rp-l (le (at r 'rp-k) (at r s/nz))))))
        ind (f/lam [['rp-j nat] ['rp-ih (claim 'rp-j)] ['rp-hm (below (s/succ 'rp-j) K)] ['rp-k nat] ['rp-hk (below 'rp-k (s/succ (s/succ 'rp-j)))]]
                   (let [j 'rp-j j1 (s/succ j)
                         jq (call 'nat/at-most-of-successor-at-most j1 q 'rp-hm)
                         hj (call 'nat/strict-below-weaken j q jq)
                         step (at 'rp-step j jq)
                         goal (le (at r 'rp-k) (at r j1))]
                     (two-terms/split-last 'rp-k 'rp-hk j1 goal
                                           (f/lam [['rp-e (eqn 'rp-k j1)]]
                                                  (f/app (f/const* 'equality/substitution [type-level]) nat j1 'rp-k
                                                         (f/app (f/const* 'equality/symmetric [type-level]) nat 'rp-k j1 'rp-e)
                                                         (f/lam [['rp-z nat]] (le (at r 'rp-z) (at r j1))) (le-refl (at r j1))))
                                           (f/lam [['rp-l (below 'rp-k j1)]]
                                                  (le-trans (at r 'rp-k) (at r j) (at r j1) (at 'rp-ih hj 'rp-k 'rp-l) step)))))
        all (f/app (f/const* 'data/Nat.rec [prop-level]) (f/lam [['rp-n nat]] (claim 'rp-n)) base ind q)]
    (s/spec 'signed/tax-rate-prefix
            [['rp-r family] ['rp-q nat] ['rp-step (s/all-below q #(le (at r %) (at r (s/succ %))))]]
            (s/all-below K #(le (at r %) (at r q)))
            (f/lam [['idx nat] ['bound (below 'idx K)]] (at all (s/self-below q) 'idx 'bound)))))

(def top-rate-spec
  (let [[r t n R T e y] '[tr-r tr-t tr-n tr-bigr tr-bigt tr-e tr-y]
        RT (f/lam [['tr-k nat]] (mul (at r 'tr-k) (at t 'tr-k)))
        RRt (f/lam [['tr-m nat]] (mul R (at t 'tr-m)))
        sum-le (a/sum-mono RT RRt n 'tr-c (fn [k hk] (call 'signed/multiply-right-monotone (at t k) (at r k) R (at 'tr-t0 k hk) (at 'tr-rr k hk))))
        RS (a/eq-le (sum RRt n) (mul R (sum t n)) (sym (mul R (sum t n)) (sum RRt n) (call 'signed/expr-sum-value-scale-left t R n)))
        T-le (le-trans T (sum RRt n) (mul R y)
                       (le-resp (sum RT n) T (sum RRt n) (sum RRt n) (sym T (sum RT n) 'tr-ht) (refl (sum RRt n)) sum-le)
                       (le-trans (sum RRt n) (mul R (sum t n)) (mul R y) RS (call 'signed/multiply-left-monotone R (sum t n) y 'tr-r0 'tr-sum)))]
    (s/spec 'signed/tax-top-rate
            [['tr-r family] ['tr-t family] ['tr-n nat] ['tr-bigr signed] ['tr-bigt signed] ['tr-e signed] ['tr-y signed]
             ['tr-ht (eqv T (sum RT n))] ['tr-sum (le (sum t n) y)] ['tr-rr (s/all-below n #(le (at r %) R))]
             ['tr-r0 (le s/zero R)] ['tr-t0 (s/all-below n #(le s/zero (at t %)))] ['tr-ey (eqv (mul e y) T)] ['tr-pos (lt s/zero y)]]
            (le e R)
            (call 'signed/at-most-cancel-positive-right e R y 'tr-pos
                  (le-resp T (mul e y) (mul R y) (mul R y) (sym (mul e y) T 'tr-ey) (refl (mul R y)) T-le)))))

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

(def theorem-specs [clamp-spec step-spec fill-spec prefix-spec top-rate-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      two-terms/extend-environment
      nat-more/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-tax-schedule theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
