(ns rainbow.math.lemmas.weighted-median
  "General lemmas: weighted median. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
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

(defn le-refl [x] (call 'signed/at-most-reflexive x))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn eqb [x y] (f/equality type-level bool x y))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(def two center/two)

(defn sel [at-false at-true t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true t))

(defn dec [p q] (call 'signed/decide-at-most p q))

(defn absv [p x] (sel (sub p x) (sub x p) (dec p x)))

(defn right-ind [p x] (sel one s/zero (dec p x)))

(defn left-ind [p x] (sel one s/zero (dec x p)))

(defn by-bit [D goal-of on-false on-true hname]
  (f/app (f/const* 'data/Bool.rec [prop-level])
         (f/lam [['bb bool]] (f/forall [[hname (eqb D 'bb)]] (goal-of 'bb)))
         (f/lam [[hname (eqb D bfalse)]] (on-false hname))
         (f/lam [[hname (eqb D btrue)]] (on-true hname))
         D
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(def diff-reverse-spec
  (s/spec 'signed/difference-at-most-reverse [['u signed] ['v signed] ['h (le 'u 'v)]]
          (le (sub 'u 'v) (sub 'v 'u))
          (le-trans (sub 'u 'v) s/zero (sub 'v 'u)
                    (le-resp (add 'u (neg 'v)) (sub 'u 'v) (add 'v (neg 'v)) s/zero (refl (sub 'u 'v)) (ring (add 'v (neg 'v)) s/zero)
                             (call 'signed/add-right-monotone 'u 'v (neg 'v) 'h))
                    (le-resp (add 'u (neg 'u)) s/zero (add 'v (neg 'u)) (sub 'v 'u) (ring (add 'u (neg 'u)) s/zero) (refl (sub 'v 'u))
                             (call 'signed/add-right-monotone 'u 'v (neg 'u) 'h)))))

(def abs-ge-plus-spec
  (s/spec 'signed/decided-abs-at-least-difference [['p signed] ['x signed]]
          (le (sub 'p 'x) (absv 'p 'x))
          (by-bit (dec 'p 'x) #(le (sub 'p 'x) (sel (sub 'p 'x) (sub 'x 'p) %))
                  (fn [_] (le-refl (sub 'p 'x)))
                  (fn [h] (call 'signed/difference-at-most-reverse 'p 'x (call 'signed/decide-at-most-true-sound 'p 'x h)))
                  'ah)))

(def abs-ge-minus-spec
  (s/spec 'signed/decided-abs-at-least-reverse-difference [['p signed] ['x signed]]
          (le (sub 'x 'p) (absv 'p 'x))
          (by-bit (dec 'p 'x) #(le (sub 'x 'p) (sel (sub 'p 'x) (sub 'x 'p) %))
                  (fn [h] (call 'signed/difference-at-most-reverse 'x 'p (call 'signed/decide-at-most-false-reverse 'p 'x h)))
                  (fn [_] (le-refl (sub 'x 'p)))
                  'ah)))

(defn flip-when-equal [p x hpx hxp]   ; p ~ x  ->  p - x ~ x - p
  (let [e (anti p x hpx hxp)]
    (a/chain (sub p x) [(sub x x) (s/add-cong p x (neg x) (neg x) e (refl (neg x)))]
             [(sub x p) (s/add-cong x x (neg x) (neg p) (refl x) (a/neg-cong x p (sym p x e)))])))

(def abs-left-spec
  (s/spec 'signed/decided-abs-when-left [['p signed] ['x signed] ['h (le 'p 'x)]]
          (eqv (absv 'p 'x) (sub 'x 'p))
          (by-bit (dec 'p 'x) #(eqv (sel (sub 'p 'x) (sub 'x 'p) %) (sub 'x 'p))
                  (fn [hb] (flip-when-equal 'p 'x 'h (call 'signed/decide-at-most-false-reverse 'p 'x hb)))
                  (fn [_] (refl (sub 'x 'p)))
                  'ah)))

(def abs-right-spec
  (s/spec 'signed/decided-abs-when-right [['p signed] ['x signed] ['h (le 'x 'p)]]
          (eqv (absv 'p 'x) (sub 'p 'x))
          (by-bit (dec 'p 'x) #(eqv (sel (sub 'p 'x) (sub 'x 'p) %) (sub 'p 'x))
                  (fn [_] (refl (sub 'p 'x)))
                  (fn [hb] (flip-when-equal 'x 'p 'h (call 'signed/decide-at-most-true-sound 'p 'x hb)))
                  'ah)))

(defn rhs [ab i d] (sub (add ab d) (mul i (add d d))))

(defn rhs-norm [ab i d target]
  (let [dd (add d d) base (add ab d)
        [v pf] (if (= i one)
                 [(sub base dd) (s/add-cong base base (neg (mul one dd)) (neg dd) (refl base) (a/neg-cong (mul one dd) dd (call 'signed/multiply-one-left dd)))]
                 [(sub base s/zero) (s/add-cong base base (neg (mul s/zero dd)) (neg s/zero) (refl base) (a/neg-cong (mul s/zero dd) s/zero (call 'signed/multiply-zero-left dd)))])]
    (trans (rhs ab i d) v target pf (ring v target))))

(def shift-right-spec
  (let [p 'p x 'x y 'y d (sub y x)]
    (s/spec 'signed/abs-shift-right [['p signed] ['x signed] ['y signed]]
            (le (rhs (absv p x) (right-ind p x) d) (absv p y))
            (by-bit (dec p x) #(le (rhs (sel (sub p x) (sub x p) %) (sel one s/zero %) d) (absv p y))
                    ;; x < p, indicator 1: rhs ~ (p - x) + d - (d + d) ~ p - y
                    (fn [_] (le-resp (sub p y) (rhs (sub p x) one d) (absv p y) (absv p y)
                                     (sym (rhs (sub p x) one d) (sub p y) (rhs-norm (sub p x) one d (sub p y))) (refl (absv p y))
                                     (call 'signed/decided-abs-at-least-difference p y)))
                    ;; p <= x, indicator 0: rhs ~ (x - p) + d ~ y - p
                    (fn [_] (le-resp (sub y p) (rhs (sub x p) s/zero d) (absv p y) (absv p y)
                                     (sym (rhs (sub x p) s/zero d) (sub y p) (rhs-norm (sub x p) s/zero d (sub y p))) (refl (absv p y))
                                     (call 'signed/decided-abs-at-least-reverse-difference p y)))
                    'sh))))

(def shift-left-spec
  (let [p 'p x 'x y 'y e (sub x y)
        swap-abs (fn [i ab h] ; rhs(absv p x, i) ~ rhs(ab, i) from absv p x ~ ab
                   (s/add-cong (add (absv p x) e) (add ab e) (neg (mul i (add e e))) (neg (mul i (add e e)))
                               (s/add-cong (absv p x) ab e e h (refl e)) (refl (neg (mul i (add e e))))))]
    (s/spec 'signed/abs-shift-left [['p signed] ['x signed] ['y signed]]
            (le (rhs (absv p x) (left-ind p x) e) (absv p y))
            (by-bit (dec x p) #(le (rhs (absv p x) (sel one s/zero %) e) (absv p y))
                    ;; p < x (not x <= p), indicator 1: |p - x| ~ x - p, rhs ~ y - p
                    (fn [hb] (let [px (call 'signed/decide-at-most-false-reverse x p hb)]
                               (le-resp (sub y p) (rhs (absv p x) one e) (absv p y) (absv p y)
                                        (sym (rhs (absv p x) one e) (sub y p)
                                             (trans (rhs (absv p x) one e) (rhs (sub x p) one e) (sub y p)
                                                    (swap-abs one (sub x p) (call 'signed/decided-abs-when-left p x px))
                                                    (rhs-norm (sub x p) one e (sub y p))))
                                        (refl (absv p y))
                                        (call 'signed/decided-abs-at-least-reverse-difference p y))))
                    ;; x <= p, indicator 0: |p - x| ~ p - x, rhs ~ p - y
                    (fn [hb] (let [xp (call 'signed/decide-at-most-true-sound x p hb)]
                               (le-resp (sub p y) (rhs (absv p x) s/zero e) (absv p y) (absv p y)
                                        (sym (rhs (absv p x) s/zero e) (sub p y)
                                             (trans (rhs (absv p x) s/zero e) (rhs (sub p x) s/zero e) (sub p y)
                                                    (swap-abs s/zero (sub p x) (call 'signed/decided-abs-when-right p x xp))
                                                    (rhs-norm (sub p x) s/zero e (sub p y))))
                                        (refl (absv p y))
                                        (call 'signed/decided-abs-at-least-difference p y))))
                    'sh))))

(defn cost [a w x n] (sum (f/lam [['cs nat]] (mul (at w 'cs) (absv (at a 'cs) x))) n))

(defn side-weight [ind a w x n] (sum (f/lam [['sw nat]] (mul (ind (at a 'sw) x) (at w 'sw))) n))

(defn total [w n] (sum (f/lam [['tw nat]] (at w 'tw)) n))

(def weighted-expand-spec
  (let [w 'w ab 'ab d 'd i 'i dd (add 'd 'd)]
    (s/spec 'signed/weighted-shift-expand [['w signed] ['ab signed] ['d signed] ['i signed]]
            (eqv (mul w (sub (add ab d) (mul i dd))) (add (add (mul w ab) (mul w d)) (neg (mul (mul i w) dd))))
            (a/chain (mul w (sub (add ab d) (mul i dd)))
                     [(add (mul w (add ab d)) (neg (mul w (mul i dd)))) (call 'signed/multiply-subtract-expand w (add ab d) (mul i dd))]
                     [(add (add (mul w ab) (mul w d)) (neg (mul (mul i w) dd)))
                      (s/add-cong (mul w (add ab d)) (add (mul w ab) (mul w d)) (neg (mul w (mul i dd))) (neg (mul (mul i w) dd))
                                  (call 'signed/multiply-distributes-add-left w ab d)
                                  (a/neg-cong (mul w (mul i dd)) (mul (mul i w) dd)
                                              (a/chain (mul w (mul i dd)) [(mul (mul w i) dd) (sym (mul (mul w i) dd) (mul w (mul i dd)) (call 'signed/multiply-associative w i dd))]
                                                       [(mul (mul i w) dd) (mcong (mul w i) (mul i w) dd dd (call 'signed/multiply-commutative w i) (refl dd))])))]))))

(def gain-spec
  (let [C 'C W 'W S 'S d 'd dd (add 'd 'd)
        twice (le-resp (mul (mul two S) d) (mul S dd) (mul W d) (mul W d)
                       (a/chain (mul (mul two S) d) [(mul (add S S) d) (mcong (mul two S) (add S S) d d (call 'signed/two-times S) (refl d))]
                                [(mul S dd) (ring (mul (add S S) d) (mul S dd))])
                       (refl (mul W d))
                       (rmono d (mul two S) W 'hd 'hs))]
    (s/spec 'signed/median-gain [['C signed] ['W signed] ['S signed] ['d signed] ['hd (le s/zero d)] ['hs (le (mul two S) W)]]
            (le C (add (add C (mul W d)) (neg (mul S dd))))
            (le-resp (add (add C (mul S dd)) (neg (mul S dd))) C (add (add C (mul W d)) (neg (mul S dd))) (add (add C (mul W d)) (neg (mul S dd)))
                     (ring (add (add C (mul S dd)) (neg (mul S dd))) C) (refl (add (add C (mul W d)) (neg (mul S dd))))
                     (call 'signed/add-right-monotone (add C (mul S dd)) (add C (mul W d)) (neg (mul S dd))
                           (call 'signed/add-left-monotone (mul S dd) (mul W d) C twice))))))

(def sum-shift-spec
  (let [a 'a w 'w I 'I x 'x y 'y d 'd n 'n dd (add d d)
        A (f/lam [['sa nat]] (mul (at w 'sa) (absv (at a 'sa) x)))
        B (f/lam [['sb nat]] (mul (at w 'sb) d))
        E (f/lam [['se nat]] (mul (mul (at I 'se) (at w 'se)) dd))
        NE (f/lam [['sn nat]] (neg (at E 'sn)))
        P (f/lam [['sp nat]] (mul (at w 'sp) (sub (add (absv (at a 'sp) x) d) (mul (at I 'sp) dd))))
        Q (f/lam [['sq nat]] (add (add (at A 'sq) (at B 'sq)) (at NE 'sq)))
        AB (f/lam [['sr nat]] (add (at A 'sr) (at B 'sr)))
        Y (f/lam [['sy nat]] (mul (at w 'sy) (absv (at a 'sy) y)))
        SI (sum (f/lam [['si nat]] (mul (at I 'si) (at w 'si))) n)
        W (total w n) Cx (sum A n)
        per (a/sum-mono P Y n 'ma (fn [i hi] (lmono (at w i) (sub (add (absv (at a i) x) d) (mul (at I i) dd)) (absv (at a i) y) (at 'hw i hi) (at 'hpt i hi))))
        p-eq (a/chain (sum P n)
                      [(sum Q n) (a/sum-cong P Q n 'mb
                                             (fn [i _] (call 'signed/weighted-shift-expand (at w i) (absv (at a i) x) d (at I i))))]
                      [(add (sum AB n) (sum NE n)) (call 'signed/expr-sum-value-add AB NE n)]
                      [(add (add Cx (sum B n)) (neg (sum E n)))
                       (s/add-cong (sum AB n) (add Cx (sum B n)) (sum NE n) (neg (sum E n))
                                   (call 'signed/expr-sum-value-add A B n) (call 'signed/expr-sum-value-negate E n))]
                      [(add (add Cx (mul W d)) (neg (mul SI dd)))
                       (s/add-cong (add Cx (sum B n)) (add Cx (mul W d)) (neg (sum E n)) (neg (mul SI dd))
                                   (s/add-cong Cx Cx (sum B n) (mul W d) (refl Cx) (sym (mul W d) (sum B n) (call 'signed/expr-sum-value-scale-right (f/lam [['tw nat]] (at w 'tw)) d n)))
                                   (a/neg-cong (sum E n) (mul SI dd) (sym (mul SI dd) (sum E n) (call 'signed/expr-sum-value-scale-right (f/lam [['si nat]] (mul (at I 'si) (at w 'si))) dd n))))])
        base (call 'signed/median-gain Cx W SI d 'hd 'hside)]
    (s/spec 'signed/weighted-abs-shift-sum
            [['a family] ['w family] ['I family] ['x signed] ['y signed] ['d signed] ['n nat]
             ['hw (s/all-below n #(le s/zero (at w %)))]
             ['hpt (s/all-below n #(le (sub (add (absv (at a %) x) d) (mul (at I %) (add d d))) (absv (at a %) y)))]
             ['hd (le s/zero d)] ['hside (le (mul two SI) W)]]
            (le Cx (sum Y n))
            (le-trans Cx (add (add Cx (mul W d)) (neg (mul SI dd))) (sum Y n) base
                      (le-resp (sum P n) (add (add Cx (mul W d)) (neg (mul SI dd))) (sum Y n) (sum Y n) p-eq (refl (sum Y n)) per)))))

(def optimal-spec
  (let [a 'a w 'w x 'x y 'y C 'C n 'n
        R (f/lam [['ri nat]] (right-ind (at a 'ri) x))
        L (f/lam [['li nat]] (left-ind (at a 'li) x))
        nonneg-diff (fn [u v h] (le-resp (sub u u) s/zero (sub v u) (sub v u) (ring (sub u u) s/zero) (refl (sub v u))
                                         (call 'signed/add-right-monotone u v (neg u) h)))
        goal (le C (cost a w y n))
        to-C (fn [h] (le-resp (cost a w x n) C (cost a w y n) (cost a w y n) (sym C (cost a w x n) 'hC) (refl (cost a w y n)) h))]
    (s/spec 'signed/weighted-median-optimal
            [['a family] ['w family] ['x signed] ['y signed] ['C signed] ['n nat]
             ['hw (s/all-below n #(le s/zero (at w %)))]
             ['hL (le (mul two (side-weight left-ind a w x n)) (total w n))]
             ['hR (le (mul two (side-weight right-ind a w x n)) (total w n))]
             ['hC (eqv C (cost a w x n))]]
            goal
            (call 'proposition/use-disjunction (le x y) (le y x) goal (call 'signed/at-most-total x y)
                  (f/lam [['xy (le x y)]]
                         (to-C (call 'signed/weighted-abs-shift-sum a w R x y (sub y x) n 'hw
                                     (f/lam [['pi nat] ['pi-lt (below 'pi n)]] (call 'signed/abs-shift-right (at a 'pi) x y))
                                     (nonneg-diff x y 'xy) 'hR)))
                  (f/lam [['yx (le y x)]]
                         (to-C (call 'signed/weighted-abs-shift-sum a w L x y (sub x y) n 'hw
                                     (f/lam [['pi nat] ['pi-lt (below 'pi n)]] (call 'signed/abs-shift-left (at a 'pi) x y))
                                     (nonneg-diff y x 'yx) 'hL)))))))

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

(def borrowed-specs [indep/total-spec cpm/sum-negate-spec indep/subtract-expand-spec])

(def theorem-specs [diff-reverse-spec abs-ge-plus-spec abs-ge-minus-spec abs-left-spec abs-right-spec shift-right-spec shift-left-spec weighted-expand-spec gain-spec sum-shift-spec optimal-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-weighted-median borrowed-specs) (support/extend-with-shared :expr-sum-weighted-median theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.weighted-median))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
