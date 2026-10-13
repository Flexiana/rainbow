(ns rainbow.math.lemmas.ufl-gap
  "General lemmas: ufl gap. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.rational.signed.order-monotone :as monotone]
            [rainbow.math.rational.signed.unit-laws :as units]
            [rainbow.math.nat.divmod :as divmod]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn row [F i] (a/matrix-row F i))

(defn dsum "sum_{i < m} sum_{j < n} F i j" [F m n] (sum (f/lam [['i nat]] (sum (row F 'i) n)) m))

(defn eta [w] (f/lam [['wi nat]] (at w 'wi)))

(defn positive-part [t] (f/app (f/const* 'data/Bool.rec [[:succ [:zero]]]) (f/lam [['ignored (f/const* 'data/Bool [])]] (f/const* 'signed/SignedRational [])) (f/const* 'signed/zero []) t (f/app (f/const* 'signed/decide-at-most []) (f/const* 'signed/zero []) t)))

(defn all-cells [m n body]
  (f/forall [['ai nat] ['ai-bound (below 'ai m)] ['aj nat] ['aj-bound (below 'aj n)]] (body 'ai 'aj)))

(defn bool-split
  "Prove (goal) by splitting on decide-at-most 0 t: false-case gets t <= 0, true-case gets 0 <= t."
  [t goal false-case true-case]
  (let [bool (f/const* 'data/Bool []) eq-bool (fn [x y] (f/equality type-level bool x y))
        decision (call 'signed/decide-at-most s/zero t)]
    (f/app (f/app (f/const* 'data/Bool.rec [[:zero]])
                  (f/lam [['choice bool]] (f/arrow (eq-bool decision 'choice) (goal 'choice)))
                  (f/lam [['hd (eq-bool decision (f/const* 'data/false []))]]
                         (false-case (call 'signed/decide-at-most-false-reverse s/zero t 'hd)))
                  (f/lam [['hd (eq-bool decision (f/const* 'data/true []))]]
                         (true-case (call 'signed/decide-at-most-true-sound s/zero t 'hd)))
                  decision)
           (f/app (f/const* 'equality/reflexive [type-level]) bool decision))))

(defn selected [t choice]
  (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored (f/const* 'data/Bool [])]] signed) s/zero t choice))

(def positive-part-upper-spec
  (s/spec 'signed/positive-part-upper [['t signed]] (le 't (positive-part 't))
          (bool-split 't (fn [c] (le 't (selected 't c)))
                      (fn [t-np] t-np) (fn [_] (call 'signed/at-most-reflexive 't)))))

(def positive-part-nonneg-spec
  (s/spec 'signed/positive-part-nonneg [['t signed]] (le s/zero (positive-part 't))
          (bool-split 't (fn [c] (le s/zero (selected 't c)))
                      (fn [_] (call 'signed/at-most-reflexive s/zero)) (fn [t-nn] t-nn))))

(def rect-row-weights-spec
  (let [W (f/lam [['wr nat] ['wc nat]] (mul (at 'w 'wr) (at 'X 'wr 'wc)))]
    (s/spec 'signed/rect-double-sum-row-weights
            [['w family] ['X matrix] ['m nat] ['n nat]
             ['hrows (s/all-below 'm #(eqv (sum (f/lam [['rj nat]] (at 'X % 'rj)) 'n) one))]]
            (eqv (dsum W 'm 'n) (sum (eta 'w) 'm))
            (a/sum-cong (f/lam [['i nat]] (sum (row W 'i) 'n)) (eta 'w) 'm 'ri
                        (fn [i hi]
                          (let [xr (row 'X i) wi (at 'w i)]
                            (a/chain (sum (row W i) 'n)
                                     [(mul wi (sum xr 'n)) (sym (mul wi (sum xr 'n)) (sum (row W i) 'n)
                                                                (call 'signed/expr-sum-value-scale-left xr wi 'n))]
                                     [(mul wi one) (a/mul-cong wi wi (sum xr 'n) one (refl wi) (at 'hrows i hi))]
                                     [(mul one wi) (call 'signed/multiply-commutative wi one)]
                                     [wi (call 'signed/multiply-one-left wi)])))))))

(def rect-add-spec
  (let [D (f/lam [['pr nat] ['pc nat]] (add (at 'X 'pr 'pc) (at 'Y 'pr 'pc)))
        rows (f/lam [['i nat]] (add (sum (row 'X 'i) 'n) (sum (row 'Y 'i) 'n)))
        XR (f/lam [['i nat]] (sum (row 'X 'i) 'n)) YR (f/lam [['i nat]] (sum (row 'Y 'i) 'n))]
    (s/spec 'signed/rect-double-sum-add [['X matrix] ['Y matrix] ['m nat] ['n nat]]
            (eqv (dsum D 'm 'n) (add (dsum 'X 'm 'n) (dsum 'Y 'm 'n)))
            (a/chain (dsum D 'm 'n)
                     [(sum rows 'm) (a/sum-cong (f/lam [['i nat]] (sum (row D 'i) 'n)) rows 'm 'di
                                                (fn [i _] (call 'signed/expr-sum-value-add (row 'X i) (row 'Y i) 'n)))]
                     [(add (dsum 'X 'm 'n) (dsum 'Y 'm 'n)) (call 'signed/expr-sum-value-add XR YR 'm)]))))

(defn open-cost [f Y n] (sum (f/lam [['oj nat]] (mul (at f 'oj) (at Y 'oj))) n))

(defn serve-cost [c X m n] (dsum (f/lam [['si nat] ['sj nat]] (mul (at c 'si 'sj) (at X 'si 'sj))) m n))

(defn reduced [v c i j] (sub (at v i) (at c i j)))

(defn dual-use [v c m j] (sum (f/lam [['ui nat]] (positive-part (reduced v c 'ui j))) m))

(def weak-duality-spec
  (let [m 'm n 'n
        VX (f/lam [['wr nat] ['wc nat]] (mul (at 'v 'wr) (at 'X 'wr 'wc)))
        CX (f/lam [['si nat] ['sj nat]] (mul (at 'c 'si 'sj) (at 'X 'si 'sj)))
        TX (f/lam [['ti nat] ['tj nat]] (mul (reduced 'v 'c 'ti 'tj) (at 'X 'ti 'tj)))
        PY (f/lam [['pi nat] ['pj nat]] (mul (positive-part (reduced 'v 'c 'pi 'pj)) (at 'Y 'pj)))
        SX (f/lam [['qi nat] ['qj nat]] (add (at CX 'qi 'qj) (at TX 'qi 'qj)))
        sv (sum (eta 'v) m) serve (dsum CX m n) open (open-cost 'f 'Y n)
        split (a/chain sv
                       [(dsum VX m n) (sym (dsum VX m n) sv (call 'signed/rect-double-sum-row-weights 'v 'X m n 'hrows))]
                       [(dsum SX m n) (a/sum-cong (f/lam [['i nat]] (sum (row VX 'i) n)) (f/lam [['i nat]] (sum (row SX 'i) n)) m 'ci
                                                  (fn [i _] (a/sum-cong (row VX i) (row SX i) n 'cj
                                                                        (fn [j _] (ring (mul (at 'v i) (at 'X i j))
                                                                                        (add (mul (at 'c i j) (at 'X i j))
                                                                                             (mul (reduced 'v 'c i j) (at 'X i j))))))))]
                       [(add serve (dsum TX m n)) (call 'signed/rect-double-sum-add CX TX m n)])
        cellwise (a/sum-mono (f/lam [['i nat]] (sum (row TX 'i) n)) (f/lam [['i nat]] (sum (row PY 'i) n)) m 'mi
                             (fn [i hi] (a/sum-mono (row TX i) (row PY i) n 'mj
                                                    (fn [j hj]
                                                      (let [t (reduced 'v 'c i j) p (positive-part t) x (at 'X i j) y (at 'Y j)]
                                                        (le-trans (mul t x) (mul p x) (mul p y)
                                                                  (call 'signed/multiply-right-monotone x t p (at 'x0 i hi j hj)
                                                                        (call 'signed/positive-part-upper t))
                                                                  (call 'signed/multiply-left-monotone p x y
                                                                        (call 'signed/positive-part-nonneg t) (at 'xy i hi j hj))))))))
        FPY (f/lam [['fj nat]] (sum (f/lam [['fi nat]] (at PY 'fi 'fj)) m))
        UY (f/lam [['gj nat]] (mul (dual-use 'v 'c m 'gj) (at 'Y 'gj)))
        facility (a/chain (dsum PY m n)
                          [(sum FPY n) (call 'signed/expr-sum-value-swap PY n m)]
                          [(sum UY n) (a/sum-cong FPY UY n 'hj
                                                  (fn [j _] (sym (at UY j) (at FPY j)
                                                                 (call 'signed/expr-sum-value-scale-right
                                                                       (f/lam [['ui nat]] (positive-part (reduced 'v 'c 'ui j))) (at 'Y j) m))))])
        dual-bound (call 'signed/expr-sum-value-weighted-monotone-right 'Y (f/lam [['gj nat]] (dual-use 'v 'c m 'gj)) 'f n 'y0 'hdual)
        slack-bound (le-trans (dsum TX m n) (dsum PY m n) open cellwise
                              (le-resp (sum UY n) (dsum PY m n) open open (sym (dsum PY m n) (sum UY n) facility) (refl open) dual-bound))]
    (s/spec 'signed/ufl-weak-duality
            [['f family] ['c matrix] ['v family] ['Y family] ['X matrix] ['m nat] ['n nat]
             ['hdual (s/all-below n #(le (dual-use 'v 'c m %) (at 'f %)))]
             ['y0 (s/all-below n #(le s/zero (at 'Y %)))]
             ['x0 (all-cells m n #(le s/zero (at 'X %1 %2)))]
             ['xy (all-cells m n #(le (at 'X %1 %2) (at 'Y %2)))]
             ['hrows (s/all-below m #(eqv (sum (f/lam [['rj nat]] (at 'X % 'rj)) n) one))]]
            (le sv (add open serve))
            (le-resp sv sv (add serve open) (add open serve) (refl sv) (ring (add serve open) (add open serve))
                     (le-resp (add serve (dsum TX m n)) sv (add serve open) (add serve open)
                              (sym sv (add serve (dsum TX m n)) split) (refl (add serve open))
                              (call 'signed/add-left-monotone (dsum TX m n) open serve slack-bound))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn extract [ps k proof]
  (if (= 1 (count ps)) proof
      (if (zero? k) (call 'proposition/left (first ps) (conjunction (rest ps)) proof)
          (extract (rest ps) (dec k) (call 'proposition/right (first ps) (conjunction (rest ps)) proof)))))

(def theorem-specs [positive-part-upper-spec positive-part-nonneg-spec rect-row-weights-spec rect-add-spec weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env s/extend-environment a/extend-environment monotone/extend-environment units/extend-environment divmod/extend-environment pairs/extend-environment (support/extend-with :expr-sum-ufl-gap theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.ufl-gap))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
