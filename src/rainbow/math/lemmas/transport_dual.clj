(ns rainbow.math.lemmas.transport-dual
  "General lemmas: transport dual. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.ufl-gap :as rect]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn row [F i] (a/matrix-row F i))

(defn dsum [F m n] (rect/dsum F m n))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn all-cells [m n body]
  (f/forall [['ai nat] ['ai-bound (below 'ai m)] ['aj nat] ['aj-bound (below 'aj n)]] (body 'ai 'aj)))

(defn rows-equal [X s m n] (s/all-below m #(eqv (sum (f/lam [['rj nat]] (at X % 'rj)) n) (at s %))))

(defn cols-equal [X d m n] (s/all-below n #(eqv (sum (f/lam [['ci nat]] (at X 'ci %)) m) (at d %))))

(defn nonnegative-cells [X m n] (all-cells m n #(le s/zero (at X %1 %2))))

(defn cost [c X m n] (dsum (f/lam [['ki nat] ['kj nat]] (mul (at c 'ki 'kj) (at X 'ki 'kj))) m n))

(defn dual-value [s u d v m n]
  (add (sum (f/lam [['di nat]] (mul (at s 'di) (at u 'di))) m)
       (sum (f/lam [['dj nat]] (mul (at d 'dj) (at v 'dj))) n)))

(def row-supply-spec
  (let [W (f/lam [['wr nat] ['wc nat]] (mul (at 'w 'wr) (at 'X 'wr 'wc)))
        SW (f/lam [['si nat]] (mul (at 's 'si) (at 'w 'si)))]
    (s/spec 'signed/rect-double-sum-row-supplies
            [['w family] ['X matrix] ['s family] ['m nat] ['n nat] ['hrows (rows-equal 'X 's 'm 'n)]]
            (eqv (dsum W 'm 'n) (sum SW 'm))
            (a/sum-cong (f/lam [['i nat]] (sum (row W 'i) 'n)) SW 'm 'ri
                        (fn [i hi]
                          (let [xr (row 'X i) wi (at 'w i) si (at 's i)]
                            (a/chain (sum (row W i) 'n)
                                     [(mul wi (sum xr 'n)) (sym (mul wi (sum xr 'n)) (sum (row W i) 'n)
                                                                (call 'signed/expr-sum-value-scale-left xr wi 'n))]
                                     [(mul wi si) (a/mul-cong wi wi (sum xr 'n) si (refl wi) (at 'hrows i hi))]
                                     [(mul si wi) (call 'signed/multiply-commutative wi si)])))))))

(def col-demand-spec
  (let [W (f/lam [['wr nat] ['wc nat]] (mul (at 'w 'wc) (at 'X 'wr 'wc)))
        T (f/lam [['tc nat]] (sum (f/lam [['tr nat]] (at W 'tr 'tc)) 'm))
        DW (f/lam [['dj nat]] (mul (at 'd 'dj) (at 'w 'dj)))]
    (s/spec 'signed/rect-double-sum-col-demands
            [['w family] ['X matrix] ['d family] ['m nat] ['n nat] ['hcols (cols-equal 'X 'd 'm 'n)]]
            (eqv (dsum W 'm 'n) (sum DW 'n))
            (a/chain (dsum W 'm 'n)
                     [(sum T 'n) (call 'signed/expr-sum-value-swap W 'n 'm)]
                     [(sum DW 'n)
                      (a/sum-cong T DW 'n 'cj
                                  (fn [j hj]
                                    (let [xc (f/lam [['ci nat]] (at 'X 'ci j)) wj (at 'w j) dj (at 'd j)]
                                      (a/chain (at T j)
                                               [(mul wj (sum xc 'm)) (sym (mul wj (sum xc 'm)) (at T j)
                                                                          (call 'signed/expr-sum-value-scale-left xc wj 'm))]
                                               [(mul wj dj) (a/mul-cong wj wj (sum xc 'm) dj (refl wj) (at 'hcols j hj))]
                                               [(mul dj wj) (call 'signed/multiply-commutative wj dj)]))))]))))

(def weak-duality-spec
  (let [m 'm n 'n
        UV (f/lam [['lr nat] ['lc nat]] (mul (add (at 'u 'lr) (at 'v 'lc)) (at 'X 'lr 'lc)))
        UX (f/lam [['wr nat] ['wc nat]] (mul (at 'u 'wr) (at 'X 'wr 'wc)))
        VX (f/lam [['wr nat] ['wc nat]] (mul (at 'v 'wc) (at 'X 'wr 'wc)))
        SX (f/lam [['sr nat] ['sc nat]] (add (at UX 'sr 'sc) (at VX 'sr 'sc)))
        CX (f/lam [['ki nat] ['kj nat]] (mul (at 'c 'ki 'kj) (at 'X 'ki 'kj)))
        dual (dual-value 's 'u 'd 'v m n)
        split (a/chain (dsum UV m n)
                       [(dsum SX m n)
                        (a/sum-cong (f/lam [['i nat]] (sum (row UV 'i) n)) (f/lam [['i nat]] (sum (row SX 'i) n)) m 'si
                                    (fn [i _] (a/sum-cong (row UV i) (row SX i) n 'sj
                                                          (fn [j _] (a/ring-eq (mul (add (at 'u i) (at 'v j)) (at 'X i j))
                                                                               (add (mul (at 'u i) (at 'X i j)) (mul (at 'v j) (at 'X i j))))))))]
                       [(add (dsum UX m n) (dsum VX m n)) (call 'signed/rect-double-sum-add UX VX m n)]
                       [dual (s/add-cong (dsum UX m n) (sum (f/lam [['di nat]] (mul (at 's 'di) (at 'u 'di))) m)
                                         (dsum VX m n) (sum (f/lam [['dj nat]] (mul (at 'd 'dj) (at 'v 'dj))) n)
                                         (call 'signed/rect-double-sum-row-supplies 'u 'X 's m n 'hrows)
                                         (call 'signed/rect-double-sum-col-demands 'v 'X 'd m n 'hcols))])
        cellwise (a/sum-mono (f/lam [['i nat]] (sum (row UV 'i) n)) (f/lam [['i nat]] (sum (row CX 'i) n)) m 'mi
                             (fn [i hi] (a/sum-mono (row UV i) (row CX i) n 'mj
                                                    (fn [j hj] (call 'signed/multiply-right-monotone (at 'X i j)
                                                                     (add (at 'u i) (at 'v j)) (at 'c i j)
                                                                     (at 'x0 i hi j hj) (at 'hdual i hi j hj))))))]
    (s/spec 'signed/transport-weak-duality
            [['c matrix] ['u family] ['v family] ['s family] ['d family] ['X matrix] ['m nat] ['n nat]
             ['hdual (all-cells m n #(le (add (at 'u %1) (at 'v %2)) (at 'c %1 %2)))]
             ['x0 (nonnegative-cells 'X m n)] ['hrows (rows-equal 'X 's m n)] ['hcols (cols-equal 'X 'd m n)]]
            (le dual (cost 'c 'X m n))
            (le-resp (dsum UV m n) dual (dsum CX m n) (dsum CX m n) split (refl (dsum CX m n)) cellwise))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [row-supply-spec col-demand-spec weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.lemmas.ufl-gap rainbow.math.lemmas.lp-duality rainbow.math.nat.infinite rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.nnrat.identities rainbow.math.rational.signed.limit-uniqueness rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.nat.divmod rainbow.math.nat.pair-index-inverse rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.unit-laws rainbow.math.checks rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.lemmas.bb-leaf-bound])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-transport-dual theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.transport-dual))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
