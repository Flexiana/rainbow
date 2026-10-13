(ns rainbow.math.lemmas.assign-dual
  "General lemmas: assign dual. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn double-sum [F n] (a/double-sum F n))

(defn row [F i] (a/matrix-row F i))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn all-cells [n body]
  (f/forall [['ai nat] ['ai-bound (below 'ai n)] ['aj nat] ['aj-bound (below 'aj n)]] (body 'ai 'aj)))

(defn eta [w] (f/lam [['wi nat]] (at w 'wi)))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (call 'signed/multiply-one-left x)]))

(defn row-sums-one [X n] (s/all-below n #(eqv (sum (f/lam [['rj nat]] (at X % 'rj)) n) one)))

(defn col-sums-one [X n] (s/all-below n #(eqv (sum (f/lam [['ci nat]] (at X 'ci %)) n) one)))

(defn nonnegative-cells [X n] (all-cells n #(le s/zero (at X %1 %2))))

(defn cost [c X n] (double-sum (f/lam [['ki nat] ['kj nat]] (mul (at c 'ki 'kj) (at X 'ki 'kj))) n))

(def row-weights-spec
  (let [W (f/lam [['wr nat] ['wc nat]] (mul (at 'w 'wr) (at 'X 'wr 'wc)))]
    (s/spec 'signed/double-sum-row-weights [['w family] ['X matrix] ['n nat] ['hrows (row-sums-one 'X 'n)]]
            (eqv (double-sum W 'n) (sum (eta 'w) 'n))
            (a/sum-cong (f/lam [['i nat]] (sum (row W 'i) 'n)) (eta 'w) 'n 'ri
                        (fn [i hi]
                          (let [xr (row 'X i) wi (at 'w i)]
                            (a/chain (sum (row W i) 'n)
                                     [(mul wi (sum xr 'n)) (sym (mul wi (sum xr 'n)) (sum (row W i) 'n)
                                                                (call 'signed/expr-sum-value-scale-left xr wi 'n))]
                                     [(mul wi one) (a/mul-cong wi wi (sum xr 'n) one (refl wi) (at 'hrows i hi))]
                                     [wi (times-one wi)])))))))

(def col-weights-spec
  (let [W (f/lam [['wr nat] ['wc nat]] (mul (at 'w 'wc) (at 'X 'wr 'wc)))
        T (f/lam [['tc nat]] (sum (f/lam [['tr nat]] (at W 'tr 'tc)) 'n))]
    (s/spec 'signed/double-sum-col-weights [['w family] ['X matrix] ['n nat] ['hcols (col-sums-one 'X 'n)]]
            (eqv (double-sum W 'n) (sum (eta 'w) 'n))
            (a/chain (double-sum W 'n)
                     [(sum T 'n) (call 'signed/expr-sum-value-swap W 'n 'n)]
                     [(sum (eta 'w) 'n)
                      (a/sum-cong T (eta 'w) 'n 'cj
                                  (fn [j hj]
                                    (let [xc (f/lam [['ci nat]] (at 'X 'ci j)) wj (at 'w j)]
                                      (a/chain (at T j)
                                               [(mul wj (sum xc 'n)) (sym (mul wj (sum xc 'n)) (at T j)
                                                                          (call 'signed/expr-sum-value-scale-left xc wj 'n))]
                                               [(mul wj one) (a/mul-cong wj wj (sum xc 'n) one (refl wj) (at 'hcols j hj))]
                                               [wj (times-one wj)]))))]))))

(def double-add-spec
  (let [D (f/lam [['pr nat] ['pc nat]] (add (at 'X 'pr 'pc) (at 'Y 'pr 'pc)))
        rows (f/lam [['i nat]] (add (sum (row 'X 'i) 'n) (sum (row 'Y 'i) 'n)))
        XR (f/lam [['i nat]] (sum (row 'X 'i) 'n)) YR (f/lam [['i nat]] (sum (row 'Y 'i) 'n))]
    (s/spec 'signed/double-sum-add [['X matrix] ['Y matrix] ['n nat]]
            (eqv (double-sum D 'n) (add (double-sum 'X 'n) (double-sum 'Y 'n)))
            (a/chain (double-sum D 'n)
                     [(sum rows 'n) (a/sum-cong (f/lam [['i nat]] (sum (row D 'i) 'n)) rows 'n 'di
                                                (fn [i _] (call 'signed/expr-sum-value-add (row 'X i) (row 'Y i) 'n)))]
                     [(add (double-sum 'X 'n) (double-sum 'Y 'n)) (call 'signed/expr-sum-value-add XR YR 'n)]))))

(def weak-duality-spec
  (let [n 'n
        UV (f/lam [['lr nat] ['lc nat]] (mul (add (at 'u 'lr) (at 'v 'lc)) (at 'X 'lr 'lc)))
        UX (f/lam [['wr nat] ['wc nat]] (mul (at 'u 'wr) (at 'X 'wr 'wc)))
        VX (f/lam [['wr nat] ['wc nat]] (mul (at 'v 'wc) (at 'X 'wr 'wc)))
        SX (f/lam [['sr nat] ['sc nat]] (add (at UX 'sr 'sc) (at VX 'sr 'sc)))
        CX (f/lam [['ki nat] ['kj nat]] (mul (at 'c 'ki 'kj) (at 'X 'ki 'kj)))
        dual (add (sum (eta 'u) n) (sum (eta 'v) n))
        split (a/chain (double-sum UV n)
                       [(double-sum SX n)
                        (a/sum-cong (f/lam [['i nat]] (sum (row UV 'i) n)) (f/lam [['i nat]] (sum (row SX 'i) n)) n 'si
                                    (fn [i _] (a/sum-cong (row UV i) (row SX i) n 'sj
                                                          (fn [j _] (a/ring-eq (mul (add (at 'u i) (at 'v j)) (at 'X i j))
                                                                               (add (mul (at 'u i) (at 'X i j)) (mul (at 'v j) (at 'X i j))))))))]
                       [(add (double-sum UX n) (double-sum VX n)) (call 'signed/double-sum-add UX VX n)]
                       [dual (s/add-cong (double-sum UX n) (sum (eta 'u) n) (double-sum VX n) (sum (eta 'v) n)
                                         (call 'signed/double-sum-row-weights 'u 'X n 'hrows)
                                         (call 'signed/double-sum-col-weights 'v 'X n 'hcols))])
        cellwise (a/sum-mono (f/lam [['i nat]] (sum (row UV 'i) n)) (f/lam [['i nat]] (sum (row CX 'i) n)) n 'mi
                             (fn [i hi] (a/sum-mono (row UV i) (row CX i) n 'mj
                                                    (fn [j hj] (call 'signed/multiply-right-monotone (at 'X i j)
                                                                     (add (at 'u i) (at 'v j)) (at 'c i j)
                                                                     (at 'x0 i hi j hj) (at 'hdual i hi j hj))))))]
    (s/spec 'signed/assignment-weak-duality
            [['c matrix] ['u family] ['v family] ['X matrix] ['n nat]
             ['hdual (all-cells n #(le (add (at 'u %1) (at 'v %2)) (at 'c %1 %2)))]
             ['x0 (nonnegative-cells 'X n)] ['hrows (row-sums-one 'X n)] ['hcols (col-sums-one 'X n)]]
            (le dual (cost 'c 'X n))
            (le-resp (double-sum UV n) dual (double-sum CX n) (double-sum CX n) split (refl (double-sum CX n)) cellwise))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [row-weights-spec col-weights-spec double-add-spec weak-duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      s/extend-environment
      a/extend-environment
      units/extend-environment
      divmod/extend-environment
      pairs/extend-environment
      (support/extend-with :expr-sum-assign-dual theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
