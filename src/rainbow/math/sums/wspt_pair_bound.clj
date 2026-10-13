(ns rainbow.math.sums.wspt-pair-bound
  "Pairwise lower bound for a prefix completion objective, exact for sorted pairs.
  Generic finite sequences only; the permutation bridge is separate."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add mul le eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.triangular :as tr]
            [rainbow.math.sums.wspt-order :as order]))
(defn minimum [x y] (call 'signed/min x y))
(defn pair-matrix [P W]
  (f/lam [['pb-i nat] ['pb-j nat]]
    (minimum (mul (at P 'pb-i) (at W 'pb-j)) (mul (at P 'pb-j) (at W 'pb-i)))))
(defn pair-expression [P W n]
  (add (tr/diagonal (tr/products P W) n) (tr/square (pair-matrix P W) n)))
(defn ordered-pairs [P W n]
  (f/forall [['pb-later nat] ['pb-later-bound (s/below 'pb-later n)]
             ['pb-earlier nat] ['pb-earlier-bound (s/below 'pb-earlier 'pb-later)]]
    (le (mul (at P 'pb-earlier) (at W 'pb-later))
        (mul (at P 'pb-later) (at W 'pb-earlier)))))
(def min-respects-spec
  (s/spec 'signed/wspt-min-respects-equivalence
    [['pb-a signed] ['pb-b signed] ['pb-c signed] ['pb-d signed]
     ['pb-ac (eqv 'pb-a 'pb-c)] ['pb-bd (eqv 'pb-b 'pb-d)]]
    (eqv (minimum 'pb-a 'pb-b) (minimum 'pb-c 'pb-d))
    (call 'signed/at-most-antisymmetric (minimum 'pb-a 'pb-b) (minimum 'pb-c 'pb-d)
      (call 'signed/min-monotone 'pb-a 'pb-b 'pb-c 'pb-d
        (a/eq-le 'pb-a 'pb-c 'pb-ac) (a/eq-le 'pb-b 'pb-d 'pb-bd))
      (call 'signed/min-monotone 'pb-c 'pb-d 'pb-a 'pb-b
        (a/eq-le 'pb-c 'pb-a (sym 'pb-a 'pb-c 'pb-ac))
        (a/eq-le 'pb-d 'pb-b (sym 'pb-b 'pb-d 'pb-bd))))))
(defn- symmetry [P W n]
  (f/lam [['tr-i nat] ['tr-ib (s/below 'tr-i n)] ['tr-j nat] ['tr-jb (s/below 'tr-j n)]]
    (call 'signed/min-commutative (mul (at P 'tr-i) (at W 'tr-j)) (mul (at P 'tr-j) (at W 'tr-i)))))
(defn- diagonal-identity [P W n]
  (a/sum-cong
    (f/lam [['pb-di nat]] (minimum (mul (at P 'pb-di) (at W 'pb-di)) (mul (at P 'pb-di) (at W 'pb-di))))
    (f/lam [['pb-di nat]] (mul (at P 'pb-di) (at W 'pb-di))) n 'pb-diag
    (fn [i _] (call 'signed/min-idempotent (mul (at P i) (at W i))))))
(def components-spec
  (let [P 'pb-times W 'pb-weights n 'pb-size M (tr/products P W) K (pair-matrix P W)
        D (tr/diagonal M n) DK (tr/diagonal K n) T (tr/triangle K n) base (add T D)]
    (s/spec 'signed/wspt-pair-expression-decomposition [[P family] [W family] [n nat]]
      (eqv (pair-expression P W n) (add base base))
      (a/chain (pair-expression P W n)
        [(add D (add (add T T) DK))
         (s/add-cong D D (tr/square K n) (add (add T T) DK) (refl D)
           (call 'signed/expr-sum-symmetric-triangular K n (symmetry P W n)))]
        [(add D (add (add T T) D))
         (s/add-cong D D (add (add T T) DK) (add (add T T) D) (refl D)
           (s/add-cong (add T T) (add T T) DK D (refl (add T T)) (diagonal-identity P W n)))]
        [(add base base) (a/ring-eq (add D (add (add T T) D)) (add base base))]))))
(def lower-spec
  (let [P 'pb-times W 'pb-weights n 'pb-size M (tr/products P W) K (pair-matrix P W)
        T (tr/triangle M n) TK (tr/triangle K n) D (tr/diagonal M n)
        F (tr/completion-cost P W n) low (add TK D) high (add T D)
        triangle-bound (a/sum-mono
                         (f/lam [['pb-k nat]] (sum (tr/column K 'pb-k) 'pb-k))
                         (f/lam [['pb-k nat]] (sum (tr/column M 'pb-k) 'pb-k)) n 'pb-k0
                         (fn [k _] (a/sum-mono (tr/column K k) (tr/column M k) k 'pb-i0
                           (fn [i _] (call 'signed/min-lower-left (mul (at P i) (at W k)) (mul (at P k) (at W i)))))))
        bound (call 'signed/add-right-monotone TK T D triangle-bound)
        Fsame (call 'signed/expr-sum-prefix-completion-cost P W n)]
    (s/spec 'signed/wspt-pair-expression-lower-bound [[P family] [W family] [n nat]]
      (le (pair-expression P W n) (add F F))
      (s/le-transport (add low low) (pair-expression P W n) (add high high) (add F F)
        (sym (pair-expression P W n) (add low low) (call 'signed/wspt-pair-expression-decomposition P W n))
        (s/add-cong high F high F (sym F high Fsame) (sym F high Fsame))
        (call 'signed/add-monotone low high low high bound bound)))))
(def attained-spec
  (let [P 'pb-times W 'pb-weights n 'pb-size M (tr/products P W) K (pair-matrix P W)
        T (tr/triangle M n) TK (tr/triangle K n) D (tr/diagonal M n)
        F (tr/completion-cost P W n) low (add TK D) high (add T D)
        triangle-same (a/sum-cong
                        (f/lam [['pb-k nat]] (sum (tr/column K 'pb-k) 'pb-k))
                        (f/lam [['pb-k nat]] (sum (tr/column M 'pb-k) 'pb-k)) n 'pb-k1
                        (fn [k hk] (a/sum-cong (tr/column K k) (tr/column M k) k 'pb-i1
                          (fn [i hi] (call 'signed/wspt-min-of-ordered (mul (at P i) (at W k))
                                       (mul (at P k) (at W i)) (at 'pb-ordered k hk i hi))))))
        low-high (s/add-cong TK T D D triangle-same (refl D))
        Fsame (call 'signed/expr-sum-prefix-completion-cost P W n)]
    (s/spec 'signed/wspt-sorted-attains-pair-expression
      [[P family] [W family] [n nat] ['pb-ordered (ordered-pairs P W n)]]
      (eqv (pair-expression P W n) (add F F))
      (a/chain (pair-expression P W n)
        [(add low low) (call 'signed/wspt-pair-expression-decomposition P W n)]
        [(add high high) (s/add-cong low high low high low-high low-high)]
        [(add F F) (s/add-cong high F high F (sym F high Fsame) (sym F high Fsame))]))))
(def theorem-specs [min-respects-spec components-spec lower-spec attained-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (reduce (fn [checked spec] (println :wspt-pair-bound :installing (:name spec)) (flush) (support/add-spec-shared checked :expr-sum-wspt-pair-bound spec)) (-> env order/extend-environment tr/extend-environment) theorem-specs))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.wspt-pair-bound))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
