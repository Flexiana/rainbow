(ns rainbow.math.lemmas.benders-cut
  "General lemmas: benders cut. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.game-value :as game]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def cube (f/arrow nat matrix))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn dot [u v n] (sum (f/lam [['di nat]] (mul (at u 'di) (at v 'di))) n))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn all-scenarios
  "forall sc < S, (body sc) -- a DISTINCT outer binder, so s/all-below (which binds idx) can nest inside."
  [S body] (f/forall [['sc nat] ['sc-bound (below 'sc S)]] (body 'sc)))

(defn all-cells [m n body]
  (f/forall [['ai nat] ['ai-bound (below 'ai m)] ['aj nat] ['aj-bound (below 'aj n)]] (body 'ai 'aj)))

(def recourse-spec
  (let [pr (sum (f/lam [['ri nat]] (mul (at 'pi 'ri) (at 'r 'ri))) 'm2)
        pay (game/payoff 'W 'pi 'y 'm2 'n2)
        colform (sum (f/lam [['cj nat]] (mul (game/column 'W 'pi 'm2 'cj) (at 'y 'cj))) 'n2)
        qy (sum (f/lam [['qj nat]] (mul (at 'q 'qj) (at 'y 'qj))) 'n2)
        to-pay (a/sum-cong (f/lam [['ri nat]] (mul (at 'pi 'ri) (at 'r 'ri)))
                           (f/lam [['i nat]] (mul (at 'pi 'i) (game/row 'W 'y 'n2 'i))) 'm2 'fi
                           (fn [i hi] (a/mul-cong (at 'pi i) (at 'pi i) (at 'r i) (game/row 'W 'y 'n2 i) (refl (at 'pi i))
                                                  (sym (game/row 'W 'y 'n2 i) (at 'r i) (at 'feas i hi)))))]
    (s/spec 'signed/recourse-weak-duality
            [['q family] ['W matrix] ['pi family] ['y family] ['r family] ['m2 nat] ['n2 nat]
             ['hdual (s/all-below 'n2 #(le (game/column 'W 'pi 'm2 %) (at 'q %)))]
             ['y0 (s/all-below 'n2 #(le s/zero (at 'y %)))]
             ['feas (s/all-below 'm2 #(eqv (game/row 'W 'y 'n2 %) (at 'r %)))]]
            (le pr qy)
            (le-resp colform pr qy qy
                     (sym pr colform (trans pr pay colform to-pay (call 'signed/game-payoff-column-form 'W 'pi 'y 'm2 'n2)))
                     (refl qy)
                     (call 'signed/expr-sum-value-weighted-monotone-right 'y
                           (f/lam [['cj nat]] (game/column 'W 'pi 'm2 'cj)) 'q 'n2 'y0 'hdual)))))

(defn scen-row [M s] (f/lam [['sr nat]] (at M s 'sr)))

(defn scen-mat [T s] (f/lam [['ti nat] ['tj nat]] (at T s 'ti 'tj)))

(defn rhs [H T s x m2 n1] (f/lam [['hi nat]] (sub (at H s 'hi) (game/row (scen-mat T s) x n1 'hi))))

(def cut-spec
  (let [S 'S m2 'm2 n2 'n2 n1 'n1
        qY (fn [s] (dot 'q (scen-row 'Y s) n2))
        L (fn [s] (sum (f/lam [['li nat]] (mul (at 'PI s 'li) (at (rhs 'H 'T s 'x m2 n1) 'li))) m2))
        pih (fn [s] (sum (f/lam [['hi nat]] (mul (at 'PI s 'hi) (at 'H s 'hi))) m2))
        piTx (fn [s] (game/payoff (scen-mat 'T s) (scen-row 'PI s) 'x m2 n1))
        G (f/lam [['gs nat] ['gk nat]] (game/column (scen-mat 'T 'gs) (scen-row 'PI 'gs) m2 'gk))
        betax (dot 'beta 'x n1)
        lhs (sub 'alpha betax)
        E (sum (f/lam [['es nat]] (mul (at 'p 'es) (L 'es))) S)
        rhs-total (sum (f/lam [['es nat]] (mul (at 'p 'es) (qY 'es))) S)
        ;; per scenario, L_s ~ pih_s - piTx_s
        L-split (fn [s] (a/chain (L s)
                                 [(sum (f/lam [['ki nat]] (sub (mul (at 'PI s 'ki) (at 'H s 'ki))
                                                               (mul (at 'PI s 'ki) (game/row (scen-mat 'T s) 'x n1 'ki)))) m2)
                                  (a/sum-cong (f/lam [['li nat]] (mul (at 'PI s 'li) (at (rhs 'H 'T s 'x m2 n1) 'li)))
                                              (f/lam [['ki nat]] (sub (mul (at 'PI s 'ki) (at 'H s 'ki))
                                                                      (mul (at 'PI s 'ki) (game/row (scen-mat 'T s) 'x n1 'ki)))) m2 'lr
                                              (fn [i _] (ring (mul (at 'PI s i) (sub (at 'H s i) (game/row (scen-mat 'T s) 'x n1 i)))
                                                              (sub (mul (at 'PI s i) (at 'H s i)) (mul (at 'PI s i) (game/row (scen-mat 'T s) 'x n1 i))))))]
                                 [(sub (pih s) (piTx s))
                                  (call 'signed/expr-sum-value-subtract
                                        (f/lam [['hi nat]] (mul (at 'PI s 'hi) (at 'H s 'hi)))
                                        (f/lam [['ti nat]] (mul (at (scen-row 'PI s) 'ti) (game/row (scen-mat 'T s) 'x n1 'ti))) m2)]))
        PA (sum (f/lam [['as nat]] (mul (at 'p 'as) (pih 'as))) S)
        PT (sum (f/lam [['bs nat]] (mul (at 'p 'bs) (piTx 'bs))) S)
        PG (sum (f/lam [['cs nat]] (mul (at 'p 'cs) (dot (scen-row G 'cs) 'x n1))) S)
        E-split (a/chain E
                         [(sum (f/lam [['es nat]] (sub (mul (at 'p 'es) (pih 'es)) (mul (at 'p 'es) (piTx 'es)))) S)
                          (a/sum-cong (f/lam [['es nat]] (mul (at 'p 'es) (L 'es)))
                                      (f/lam [['es nat]] (sub (mul (at 'p 'es) (pih 'es)) (mul (at 'p 'es) (piTx 'es)))) S 'eu
                                      (fn [s _] (trans (mul (at 'p s) (L s)) (mul (at 'p s) (sub (pih s) (piTx s)))
                                                       (sub (mul (at 'p s) (pih s)) (mul (at 'p s) (piTx s)))
                                                       (a/mul-cong (at 'p s) (at 'p s) (L s) (sub (pih s) (piTx s)) (refl (at 'p s)) (L-split s))
                                                       (ring (mul (at 'p s) (sub (pih s) (piTx s)))
                                                             (sub (mul (at 'p s) (pih s)) (mul (at 'p s) (piTx s)))))))]
                         [(sub PA PT) (call 'signed/expr-sum-value-subtract
                                            (f/lam [['as nat]] (mul (at 'p 'as) (pih 'as))) (f/lam [['bs nat]] (mul (at 'p 'bs) (piTx 'bs))) S)])
        ;; PT ~ PG (within-scenario exchange) ~ beta.x (across-scenario exchange + hbeta)
        PT-PG (a/sum-cong (f/lam [['bs nat]] (mul (at 'p 'bs) (piTx 'bs))) (f/lam [['cs nat]] (mul (at 'p 'cs) (dot (scen-row G 'cs) 'x n1))) S 'ps
                          (fn [s _] (a/mul-cong (at 'p s) (at 'p s) (piTx s) (dot (scen-row G s) 'x n1) (refl (at 'p s))
                                                (call 'signed/game-payoff-column-form (scen-mat 'T s) (scen-row 'PI s) 'x m2 n1))))
        bx (sum (f/lam [['bj nat]] (mul (game/column G 'p S 'bj) (at 'x 'bj))) n1)
        PG-bx (call 'signed/game-payoff-column-form G 'p 'x S n1)
        bx-betax (a/sum-cong (f/lam [['bj nat]] (mul (game/column G 'p S 'bj) (at 'x 'bj))) (f/lam [['di nat]] (mul (at 'beta 'di) (at 'x 'di))) n1 'bb
                             (fn [j hj] (a/mul-cong (game/column G 'p S j) (at 'beta j) (at 'x j) (at 'x j)
                                                    (sym (at 'beta j) (game/column G 'p S j) (at 'hbeta j hj)) (refl (at 'x j)))))
        E-eq (a/chain E [(sub PA PT) E-split]
                      [(sub 'alpha betax)
                       (s/add-cong PA 'alpha (neg PT) (neg betax) (sym 'alpha PA 'halpha)
                                   (a/neg-cong PT betax (a/chain PT [PG PT-PG] [bx PG-bx] [betax bx-betax])))])
        scen-bound (call 'signed/expr-sum-value-weighted-monotone-left 'p
                         (f/lam [['es nat]] (L 'es)) (f/lam [['es nat]] (qY 'es)) S 'p0
                         (f/lam [['sc nat] ['sb (below 'sc S)]]
                                (call 'signed/recourse-weak-duality 'q 'W (scen-row 'PI 'sc) (scen-row 'Y 'sc) (rhs 'H 'T 'sc 'x m2 n1) m2 n2
                                      (at 'hdual 'sc 'sb) (at 'Y0 'sc 'sb) (at 'feas 'sc 'sb))))]
    (s/spec 'signed/benders-cut-valid
            [['q family] ['W matrix] ['H matrix] ['T cube] ['PI matrix] ['p family] ['alpha signed] ['beta family]
             ['x family] ['Y matrix] ['S nat] ['m2 nat] ['n2 nat] ['n1 nat]
             ['hdual (all-scenarios S (fn [sc] (s/all-below n2 #(le (game/column 'W (scen-row 'PI sc) m2 %) (at 'q %)))))]
             ['p0 (s/all-below S #(le s/zero (at 'p %)))]
             ['halpha (eqv 'alpha (sum (f/lam [['as nat]] (mul (at 'p 'as) (sum (f/lam [['hi nat]] (mul (at 'PI 'as 'hi) (at 'H 'as 'hi))) m2))) S))]
             ['hbeta (s/all-below n1 #(eqv (at 'beta %) (game/column G 'p S %)))]
             ['Y0 (all-scenarios S (fn [sc] (s/all-below n2 #(le s/zero (at 'Y sc %)))))]
             ['feas (all-scenarios S (fn [sc] (s/all-below m2 #(eqv (game/row 'W (scen-row 'Y sc) n2 %) (at (rhs 'H 'T sc 'x m2 n1) %)))))]]
            (le lhs rhs-total)
            (le-resp E lhs rhs-total rhs-total E-eq (refl rhs-total) scen-bound))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [recourse-spec cut-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      game/extend-environment
      rectangular-index/extend-environment
      pairs/extend-environment
      (support/extend-with :expr-sum-benders-cut theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
