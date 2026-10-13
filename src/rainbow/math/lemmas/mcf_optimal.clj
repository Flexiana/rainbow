(ns rainbow.math.lemmas.mcf-optimal
  "General lemmas: mcf optimal. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.order-monotone :as monotone]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn double-sum [F n] (a/double-sum F n))

(def arc-spec
  (let [rf (mul 'rc 'f) rg (mul 'rc 'g) ru (mul 'rc 'u) goal (le rf rg)
        bool (f/const* 'data/Bool [])
        eq-bool (fn [x y] (f/equality type-level bool x y))
        decision (call 'signed/decide-at-most s/zero 'rc)
        true-case
        (f/lam [['hd (eq-bool decision (f/const* 'data/true []))]]
               (let [hrc (call 'signed/decide-at-most-true-sound s/zero 'rc 'hd)]
                 (le-trans rf s/zero rg 'hf
                           (le-resp (mul 'rc s/zero) s/zero rg rg (ring (mul 'rc s/zero) s/zero) (refl rg)
                                    (call 'signed/multiply-left-monotone 'rc s/zero 'g hrc 'hg0)))))
        false-case
        (f/lam [['hd (eq-bool decision (f/const* 'data/false []))]]
               (let [rc-np (call 'signed/decide-at-most-false-reverse s/zero 'rc 'hd)
                     nr (neg 'rc)
                     hnr (le-resp (add 'rc nr) s/zero (add s/zero nr) nr
                                  (ring (add 'rc nr) s/zero) (ring (add s/zero nr) nr)
                                  (call 'signed/add-right-monotone 'rc s/zero nr rc-np))
                     slack (mul 'rc (sub 'u 'f))
                     f-to-u (le-resp (add s/zero rf) rf (add slack rf) ru
                                     (ring (add s/zero rf) rf) (ring (add slack rf) ru)
                                     (call 'signed/add-right-monotone s/zero slack rf 'hs))
                     tail (add ru rg)
                     u-to-g (le-resp (add (mul nr 'g) tail) ru (add (mul nr 'u) tail) rg
                                     (ring (add (mul nr 'g) tail) ru) (ring (add (mul nr 'u) tail) rg)
                                     (call 'signed/add-right-monotone (mul nr 'g) (mul nr 'u) tail
                                           (call 'signed/multiply-left-monotone nr 'g 'u hnr 'hgu)))]
                 (le-trans rf ru rg f-to-u u-to-g)))]
    (s/spec 'signed/reduced-cost-arc-order
            [['rc signed] ['f signed] ['g signed] ['u signed]
             ['hg0 (le s/zero 'g)] ['hgu (le 'g 'u)] ['hf (le rf s/zero)] ['hs (le s/zero (mul 'rc (sub 'u 'f)))]]
            goal
            (f/app (f/app (f/const* 'data/Bool.rec [[:zero]])
                          (f/lam [['choice bool]] (f/arrow (eq-bool decision 'choice) goal))
                          false-case true-case decision)
                   (f/app (f/const* 'equality/reflexive [type-level]) bool decision)))))

(defn row [F i] (a/matrix-row F i))

(defn pointwise [op X Y] (f/lam [['pi-row nat] ['pi-col nat]] (op (at X 'pi-row 'pi-col) (at Y 'pi-row 'pi-col))))

(defn cost [c x n] (double-sum (pointwise mul c x) n))

(defn rc-at [c pot i j] (add (add (at c i j) (at pot i)) (neg (at pot j))))

(defn reduced-cost [c pot]
  (f/lam [['rc-row nat] ['rc-col nat]] (add (add (at c 'rc-row 'rc-col) (at pot 'rc-row)) (neg (at pot 'rc-col)))))

(defn net [x n i] (a/divergence x n i))

(defn all-arcs [n body]
  (f/forall [['ai nat] ['ai-bound (below 'ai n)] ['aj nat] ['aj-bound (below 'aj n)]] (body 'ai 'aj)))

(def double-subtract-spec
  (let [D (pointwise sub 'X 'Y)
        rows (f/lam [['i nat]] (sub (sum (row 'X 'i) 'n) (sum (row 'Y 'i) 'n)))
        XR (f/lam [['i nat]] (sum (row 'X 'i) 'n)) YR (f/lam [['i nat]] (sum (row 'Y 'i) 'n))]
    (s/spec 'signed/double-sum-subtract [['X matrix] ['Y matrix] ['n nat]]
            (eqv (double-sum D 'n) (sub (double-sum 'X 'n) (double-sum 'Y 'n)))
            (a/chain (double-sum D 'n)
                     [(sum rows 'n) (a/sum-cong (f/lam [['i nat]] (sum (row D 'i) 'n)) rows 'n 'di
                                                (fn [i _] (call 'signed/expr-sum-value-subtract (row 'X i) (row 'Y i) 'n)))]
                     [(sub (double-sum 'X 'n) (double-sum 'Y 'n)) (call 'signed/expr-sum-value-subtract XR YR 'n)]))))

(def divergence-zero-spec
  (let [D (pointwise sub 'G 'F)
        outG (a/outflow 'G 'n 'i) outF (a/outflow 'F 'n 'i) inG (a/inflow 'G 'n 'i) inF (a/inflow 'F 'n 'i)
        split-out (call 'signed/expr-sum-value-subtract (row 'G 'i) (row 'F 'i) 'n)
        split-in (call 'signed/expr-sum-value-subtract (a/matrix-col 'G 'i) (a/matrix-col 'F 'i) 'n)]
    (s/spec 'signed/divergence-difference-zero
            [['G matrix] ['F matrix] ['b family] ['n nat]
             ['hG (s/all-below 'n #(eqv (net 'G 'n %) (at 'b %)))] ['hF (s/all-below 'n #(eqv (net 'F 'n %) (at 'b %)))]
             ['i nat] ['hi (below 'i 'n)]]
            (eqv (net D 'n 'i) s/zero)
            (a/chain (net D 'n 'i)
                     [(sub (sub outG outF) (sub inG inF))
                      (s/add-cong (a/outflow D 'n 'i) (sub outG outF) (neg (a/inflow D 'n 'i)) (neg (sub inG inF))
                                  split-out (a/neg-cong (a/inflow D 'n 'i) (sub inG inF) split-in))]
                     [(sub (net 'G 'n 'i) (net 'F 'n 'i)) (ring (sub (sub outG outF) (sub inG inF)) (sub (net 'G 'n 'i) (net 'F 'n 'i)))]
                     [(sub (at 'b 'i) (at 'b 'i))
                      (s/add-cong (net 'G 'n 'i) (at 'b 'i) (neg (net 'F 'n 'i)) (neg (at 'b 'i))
                                  (at 'hG 'i 'hi) (a/neg-cong (net 'F 'n 'i) (at 'b 'i) (at 'hF 'i 'hi)))]
                     [s/zero (ring (sub (at 'b 'i) (at 'b 'i)) s/zero)]))))

(def cost-optimal-spec
  (let [n 'n rc (reduced-cost 'c 'pot) D (pointwise sub 'g 'f)
        cf (cost 'c 'f n) cg (cost 'c 'g n) diff (sub cg cf)
        p-at (fn [i j] (sub (mul (rc-at 'c 'pot i j) (at 'g i j)) (mul (rc-at 'c 'pot i j) (at 'f i j))))
        q-at (fn [i j] (mul (sub (at 'pot i) (at 'pot j)) (sub (at 'g i j) (at 'f i j))))
        P (f/lam [['pr nat] ['pc nat]] (p-at 'pr 'pc))
        Q (f/lam [['qr nat] ['qc nat]] (q-at 'qr 'qc))
        PQ (pointwise sub P Q)
        CD (pointwise sub (pointwise mul 'c 'g) (pointwise mul 'c 'f))
        weighted (f/lam [['wi nat]] (mul (at 'pot 'wi) (net D n 'wi)))
        Z (f/lam [['zi nat]] s/zero)
        q-zero (a/chain (double-sum Q n)
                        [(sum weighted n) (sym (sum weighted n) (double-sum Q n) (call 'signed/expr-sum-weighted-divergence D 'pot n))]
                        [(sum Z n) (a/sum-cong weighted Z n 'wz
                                               (fn [i hi] (a/chain (at weighted i)
                                                                   [(mul (at 'pot i) s/zero)
                                                                    (a/mul-cong (at 'pot i) (at 'pot i) (net D n i) s/zero (refl (at 'pot i))
                                                                                (call 'signed/divergence-difference-zero 'g 'f 'b n 'gnet 'fnet i hi))]
                                                                   [s/zero (ring (mul (at 'pot i) s/zero) s/zero)])))]
                        [s/zero (call 'signed/expr-sum-value-zero n)])
        diff-eq (a/chain diff
                         [(double-sum CD n) (sym (double-sum CD n) diff (call 'signed/double-sum-subtract (pointwise mul 'c 'g) (pointwise mul 'c 'f) n))]
                         [(double-sum PQ n)
                          (a/sum-cong (f/lam [['i nat]] (sum (row CD 'i) n)) (f/lam [['i nat]] (sum (row PQ 'i) n)) n 'ei
                                      (fn [i _] (a/sum-cong (row CD i) (row PQ i) n 'ej
                                                            (fn [j _] (ring (sub (mul (at 'c i j) (at 'g i j)) (mul (at 'c i j) (at 'f i j)))
                                                                            (sub (p-at i j) (q-at i j)))))))]
                         [(sub (double-sum P n) (double-sum Q n)) (call 'signed/double-sum-subtract P Q n)]
                         [(sub (double-sum P n) s/zero)
                          (s/add-cong (double-sum P n) (double-sum P n) (neg (double-sum Q n)) (neg s/zero)
                                      (refl (double-sum P n)) (a/neg-cong (double-sum Q n) s/zero q-zero))]
                         [(double-sum P n) (ring (sub (double-sum P n) s/zero) (double-sum P n))])
        Z2 (f/lam [['zr nat] ['zc nat]] s/zero)
        zero-double (a/chain (double-sum Z2 n)
                             [(sum Z n) (a/sum-cong (f/lam [['i nat]] (sum (row Z2 'i) n)) Z n 'zz
                                                    (fn [_ _] (call 'signed/expr-sum-value-zero n)))]
                             [s/zero (call 'signed/expr-sum-value-zero n)])
        arc-nonneg (fn [i j hi hj]
                     (let [rf (mul (rc-at 'c 'pot i j) (at 'f i j)) rg (mul (rc-at 'c 'pot i j) (at 'g i j))]
                       (le-resp (add rf (neg rf)) s/zero (add rg (neg rf)) (p-at i j)
                                (ring (add rf (neg rf)) s/zero) (refl (p-at i j))
                                (call 'signed/add-right-monotone rf rg (neg rf)
                                      (call 'signed/reduced-cost-arc-order (rc-at 'c 'pot i j) (at 'f i j) (at 'g i j) (at 'u i j)
                                            (at 'g0 i hi j hj) (at 'gu i hi j hj) (at 'hf i hi j hj) (at 'hs i hi j hj))))))
        p-nonneg (le-resp (double-sum Z2 n) s/zero (double-sum P n) (double-sum P n) zero-double (refl (double-sum P n))
                          (a/sum-mono (f/lam [['i nat]] (sum (row Z2 'i) n)) (f/lam [['i nat]] (sum (row P 'i) n)) n 'mi
                                      (fn [i hi] (a/sum-mono (row Z2 i) (row P i) n 'mj (fn [j hj] (arc-nonneg i j hi hj))))))
        diff-nonneg (le-resp s/zero s/zero (double-sum P n) diff (refl s/zero) (sym diff (double-sum P n) diff-eq) p-nonneg)]
    (s/spec 'signed/mcf-cost-optimal
            [['c matrix] ['u matrix] ['f matrix] ['g matrix] ['pot family] ['b family] ['n nat]
             ['f0 (all-arcs n #(le s/zero (at 'f %1 %2)))] ['fu (all-arcs n #(le (at 'f %1 %2) (at 'u %1 %2)))]
             ['g0 (all-arcs n #(le s/zero (at 'g %1 %2)))] ['gu (all-arcs n #(le (at 'g %1 %2) (at 'u %1 %2)))]
             ['fnet (s/all-below n #(eqv (net 'f n %) (at 'b %)))] ['gnet (s/all-below n #(eqv (net 'g n %) (at 'b %)))]
             ['hf (all-arcs n #(le (mul (at rc %1 %2) (at 'f %1 %2)) s/zero))]
             ['hs (all-arcs n #(le s/zero (mul (at rc %1 %2) (sub (at 'u %1 %2) (at 'f %1 %2)))))]]
            (le cf cg)
            (le-resp (add s/zero cf) cf (add diff cf) cg (ring (add s/zero cf) cf) (ring (add diff cf) cg)
                     (call 'signed/add-right-monotone s/zero diff cf diff-nonneg)))))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [parts k proof]
  (if (= 1 (count parts)) proof
      (if (zero? k) (call 'proposition/left (first parts) (conjunction (rest parts)) proof)
          (extract (rest parts) (dec k)
                   (call 'proposition/right (first parts) (conjunction (rest parts)) proof)))))

(def theorem-specs [arc-spec double-subtract-spec divergence-zero-spec cost-optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      s/extend-environment
      a/extend-environment
      monotone/extend-environment
      units/extend-environment
      divmod/extend-environment
      pairs/extend-environment
      (support/extend-with :expr-sum-mcf-optimal theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
