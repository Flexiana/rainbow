(ns rainbow.math.lemmas.matching-cover-duality
  "General lemmas: matching cover duality. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed zero family call at sum add mul eqv le refl sym]]
            [rainbow.math.sums.flow-cut :as a :refer [one sub nadd nmul nlt matrix ring-eq chain sum-cong sum-mono
                     matrix-row matrix-col le-trans]]
            [rainbow.module :as module]))

(defn pairs [p q P]
  (f/forall [['u nat] ['hu (nlt 'u p)] ['v nat] ['hv (nlt 'v q)]] (P 'u 'v)))

(defn pair-proof [p q proof]
  (f/lam [['u nat] ['hu (nlt 'u p)] ['v nat] ['hv (nlt 'v q)]] (proof 'u 'hu 'v 'hv)))

(defn rows [X q] (f/lam [['row nat]] (sum (matrix-row X 'row) q)))

(defn cols [X p] (f/lam [['col nat]] (sum (matrix-col X 'col) p)))

(defn total [X p q] (sum (rows X q) p))

(defn cover-size [L R p q] (add (sum L p) (sum R q)))

(defn polynomial [x] (mul x (sub one x)))

(defn nonnegative [X p q] (pairs p q #(le zero (at X %1 %2))))

(defn bits [X p q] (pairs p q #(eqv (polynomial (at X %1 %2)) zero)))

(defn subgraph [X A p q] (pairs p q #(le (at X %1 %2) (at A %1 %2))))

(defn covers [A L R p q] (pairs p q #(le (at A %1 %2) (add (at L %1) (at R %2)))))

(defn degree [D n] (s/all-below n #(le (at D %) one)))

(defn positive-family [F n] (s/all-below n #(le zero (at F %))))

(defn weighted [X L R]
  (f/lam [['i nat] ['j nat]] (mul (at X 'i 'j) (add (at L 'i) (at R 'j)))))

(defn weighted-degrees [W D]
  (f/lam [['i nat]] (mul (at W 'i) (at D 'i))))

(def boolean-square-spec
  (let [x 'x square (mul x x) poly (polynomial x)
        P (eqv x zero) Q (eqv x one) goal (eqv x square)
        branch (fn [v h]
                 (chain x [v h]
                        [(mul v v) (ring-eq v (mul v v))]
                        [square (a/mul-cong v x v x (sym x v h) (sym x v h))]))]
    (s/spec 'signed/square-of-boolean-polynomial
            [['x signed] ['bit (eqv poly zero)]] goal
            (a/cases P Q goal (call 'signed/zero-one-of-boolean-polynomial x 'bit)
                     (f/lam [['h P]] (branch zero 'h))
                     (f/lam [['h Q]] (branch one 'h))))))

(def double-count-spec
  (let [X 'X L 'L R 'R p 'p q 'q W (weighted X L R)
        LL (f/lam [['i nat] ['j nat]] (mul (at L 'i) (at X 'i 'j)))
        RR (f/lam [['i nat] ['j nat]] (mul (at R 'j) (at X 'i 'j)))
        LR (rows LL q) RR0 (rows RR q)
        split (f/lam [['i nat]] (add (at LR 'i) (at RR0 'i)))
        LD (weighted-degrees L (rows X q)) RD (weighted-degrees R (cols X p))
        right-cols (f/lam [['j nat]] (sum (matrix-col RR 'j) p))
        left-eq (sum-cong LR LD p 'u
                         (fn [u _] (sym (mul (at L u) (sum (matrix-row X u) q))
                                         (sum (matrix-row LL u) q)
                                         (call 'signed/expr-sum-value-scale-left (matrix-row X u) (at L u) q))))
        right-eq (chain (total RR p q)
                        [(sum right-cols q) (call 'signed/expr-sum-value-swap RR q p)]
                        [(sum RD q)
                         (sum-cong right-cols RD q 'v
                                   (fn [v _] (sym (mul (at R v) (sum (matrix-col X v) p))
                                                   (sum (matrix-col RR v) p)
                                                   (call 'signed/expr-sum-value-scale-left (matrix-col X v) (at R v) p))))])]
    (s/spec 'signed/expr-sum-matching-cover-double-count
            [['X matrix] ['L family] ['R family] ['p nat] ['q nat]]
            (eqv (total W p q) (add (sum LD p) (sum RD q)))
            (chain (total W p q)
                   [(sum split p)
                    (sum-cong (rows W q) split p 'u
                              (fn [u _]
                                (let [S (f/lam [['j nat]] (add (at LL u 'j) (at RR u 'j)))]
                                  (chain (sum (matrix-row W u) q)
                                         [(sum S q)
                                          (sum-cong (matrix-row W u) S q 'v
                                                    (fn [v _] (ring-eq (mul (at X u v) (add (at L u) (at R v)))
                                                                          (add (mul (at L u) (at X u v))
                                                                               (mul (at R v) (at X u v))))))]
                                         [(add (at LR u) (at RR0 u))
                                          (call 'signed/expr-sum-value-add (matrix-row LL u) (matrix-row RR u) q)]))))]
                   [(add (sum LR p) (sum RR0 p)) (call 'signed/expr-sum-value-add LR RR0 p)]
                   [(add (sum LD p) (sum RD q))
                    (s/add-cong (sum LR p) (sum LD p) (sum RR0 p) (sum RD q) left-eq right-eq)]))))

(defn generic-hypotheses [X L R p q]
  [['nonnegative (nonnegative X p q)] ['bits (bits X p q)]
   ['covered (covers X L R p q)]
   ['rows (degree (rows X q) p)] ['cols (degree (cols X p) q)]
   ['left (positive-family L p)] ['right (positive-family R q)]])

(defn degree-bound [W D n hw hd]
  (let [O (f/lam [['idx nat]] one) WD (weighted-degrees W D) WO (weighted-degrees W O)
        bound (call 'signed/expr-sum-value-weighted-monotone-left W D O n hw hd)
        same (sum-cong WO W n 'i (fn [i _] (ring-eq (mul (at W i) one) (at W i))))]
    (s/le-transport (sum WD n) (sum WD n) (sum WO n) (sum W n) (refl (sum WD n)) same bound)))

(def weak-duality-spec
  (let [X 'X L 'L R 'R p 'p q 'q W (weighted X L R)
        ordered (sum-mono (rows X q) (rows W q) p 'u
                          (fn [u hu]
                            (sum-mono (matrix-row X u) (matrix-row W u) q 'v
                                      (fn [v hv]
                                        (let [x (at X u v) c (add (at L u) (at R v))
                                              same (call 'signed/square-of-boolean-polynomial x (at 'bits u hu v hv))]
                                          (s/le-transport (mul x x) x (mul x c) (mul x c)
                                                          (sym x (mul x x) same) (refl (mul x c))
                                                          (call 'signed/multiply-left-monotone x x c
                                                                (at 'nonnegative u hu v hv) (at 'covered u hu v hv))))))))
        LD (sum (weighted-degrees L (rows X q)) p)
        RD (sum (weighted-degrees R (cols X p)) q)
        count-eq (call 'signed/expr-sum-matching-cover-double-count X L R p q)
        bounded (call 'signed/add-monotone LD (sum L p) RD (sum R q)
                      (degree-bound L (rows X q) p 'left 'rows)
                      (degree-bound R (cols X p) q 'right 'cols))]
    (s/spec 'signed/expr-sum-matching-cover-weak-duality
            (into [['X matrix] ['L family] ['R family] ['p nat] ['q nat]] (generic-hypotheses X L R p q))
            (le (total X p q) (cover-size L R p q))
            (le-trans (total X p q) (total W p q) (cover-size L R p q) ordered
                      (le-trans (total W p q) (add LD RD) (cover-size L R p q)
                                (a/eq-le (total W p q) (add LD RD) count-eq) bounded)))))

(defn edge-below [p q u v hu hv]
  (a/ntrans (s/succ (nadd v (nmul u q))) (nmul (s/succ u) q) (nmul p q)
            (call 'nat/add-right-monotone (nmul u q) (s/succ v) q hv)
            (call 'nat/multiply-right-monotone q (s/succ u) p hu)))

(defn weak-proof [A X L R p q ev]
  (call 'signed/expr-sum-matching-cover-weak-duality X L R p q
        (:nonnegative ev) (:bits ev)
        (pair-proof p q (fn [u hu v hv]
                         (le-trans (at X u v) (at A u v) (add (at L u) (at R v))
                                   (at (:subgraph ev) u hu v hv) (at (:cover ev) u hu v hv))))
        (:rows ev) (:cols ev) (:left ev) (:right ev)))

(def theorem-specs [boolean-square-spec double-count-spec weak-duality-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env a/extend-environment (support/extend-with :expr-sum-matching-cover-duality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.matching-cover-duality))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
