(ns rainbow.math.sums.value-algebra
  "Finite-sum algebra for the existing signed/expr-sum-value. All regrouping
  uses signed/equivalent (Grothendieck equality), never equality of raw pairs.
  Bounds and congruences require hypotheses only below the finite bound."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.checks :as checker]
            [rainbow.math.rational.signed.map-sum-algebra :as algebra]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.sets.finset.range :as ranges]
            [rainbow.math.rational.signed.fubini :as fubini]
            [rainbow.math.rational.signed.pointwise-order :as pointwise]))

(def nat (f/const* 'data/Nat []))
(def nz (f/const* 'data/zero []))
(def signed (f/const* 'signed/SignedRational []))
(def zero (f/const* 'signed/zero []))
(def family (f/arrow nat signed))
(defn call [name & args] (apply f/app (f/const* name []) args))
(defn at [g & args] (apply f/app g args))
(defn succ [n] (call 'data/succ n))
(defn sum [g n] (call 'signed/expr-sum-value g n))
(defn add [a b] (call 'signed/add a b))
(defn mul [a b] (call 'signed/multiply a b))
(defn eqv [a b] (call 'signed/equivalent a b))
(defn le [a b] (call 'signed/at-most a b))
(defn below [i n] (call 'nat/strict-below i n))
(defn refl [a] (call 'signed/equivalent-reflexive a))
(defn sym [a b h] (call 'signed/equivalent-symmetric a b h))
(defn trans [a b c h k] (call 'signed/equivalent-transitive a b c h k))
(defn add-cong [a b c d h k] (call 'signed/add-respects-equivalence a b c d h k))
(defn all-below [n pred] (f/forall [['idx nat] ['bound (below 'idx n)]] (pred 'idx)))
(defn self-below [n] (call 'nat/at-most-reflexive (succ n)))
(defn weaken [i n h]
  (call 'nat/at-most-transitive (succ i) n (succ n) h (call 'nat/at-most-successor n)))
(defn induct [claim base step n]
  (f/app (f/const* 'data/Nat.rec [[:zero]])
         (f/lam [['k nat]] (claim 'k)) base
         (f/lam [['q nat] ['ih (claim 'q)]] (step 'q 'ih)) n))
(defn spec [name binders claim proof]
  {:name name :universes [] :type (f/forall binders claim) :value (f/lam binders proof)})

(defn indices [n] (call 'list/nat-range n))
(defn map-sum [g n]
  (f/app (f/const* 'signed/map-sum [[:zero]]) nat g (indices n)))
(defn list-law [name & args]
  (apply f/app (f/const* name [[:zero]]) nat args))
(defn bridge [g n] (call 'signed/expr-sum-value-as-map-sum g n))

;; nat-range is descending; expr-sum-value appends the new term.
(def bridge-spec
  (let [claim #(eqv (sum 'F %) (map-sum 'F %))]
    (spec 'signed/expr-sum-value-as-map-sum [['F family] ['n nat]] (claim 'n)
          (induct claim (refl zero)
                  (fn [q ih]
                    (let [a (sum 'F q) b (map-sum 'F q) c (at 'F q)]
                      (trans (add a c) (add b c) (add c b)
                             (add-cong a b c c ih (refl c))
                             (call 'signed/add-commutative b c)))) 'n))))

(def zero-spec
  (let [g (f/lam [['i nat]] zero)]
    (spec 'signed/expr-sum-value-zero [['n nat]] (eqv (sum g 'n) zero)
          (trans (sum g 'n) (map-sum g 'n) zero (bridge g 'n)
                 (list-law 'signed/map-sum-zero g
                           (f/lam [['i nat]] (refl zero)) (indices 'n))))))

(def add-spec
  (let [g (f/lam [['i nat]] (add (at 'F 'i) (at 'G 'i)))
        a (sum g 'n) b (map-sum g 'n)
        c (add (map-sum 'F 'n) (map-sum 'G 'n))
        d (add (sum 'F 'n) (sum 'G 'n))]
    (spec 'signed/expr-sum-value-add [['F family] ['G family] ['n nat]] (eqv a d)
          (trans a b d (bridge g 'n)
                 (trans b c d (list-law 'signed/map-sum-add 'F 'G (indices 'n))
                        (sym d c (add-cong (sum 'F 'n) (map-sum 'F 'n)
                                           (sum 'G 'n) (map-sum 'G 'n)
                                           (bridge 'F 'n) (bridge 'G 'n))))))))

(def scale-right-spec
  (let [g (f/lam [['i nat]] (mul (at 'F 'i) 'c))
        a (mul (sum 'F 'n) 'c) b (mul (map-sum 'F 'n) 'c)
        c (map-sum g 'n) d (sum g 'n)]
    (spec 'signed/expr-sum-value-scale-right [['F family] ['c signed] ['n nat]] (eqv a d)
          (trans a b d
                 (call 'signed/multiply-respects-equivalence
                       (sum 'F 'n) (map-sum 'F 'n) 'c 'c (bridge 'F 'n) (refl 'c))
                 (trans b c d (list-law 'signed/map-sum-scale-right 'F 'c (indices 'n))
                        (sym d c (bridge g 'n)))))))

(defn listed-le [g h n] (list-law 'signed/all-at-most g h (indices n)))
(defn le-transport [a b c d h k ordered]
  (call 'signed/at-most-respects-equivalence a b c d h k ordered))

;; Bridge the checker's bounded forall to the list lane's conjunction fold.
(def bounds-bridge-spec
  (let [hyp #(all-below % (fn [i] (le (at 'F i) (at 'G i))))
        claim #(f/forall [['H (hyp %)]] (listed-le 'F 'G %))]
    {:name 'signed/expr-sum-bounds-as-list :universes []
     :type (f/forall [['F family] ['G family] ['n nat]] (claim 'n))
     :value (f/lam [['F family] ['G family] ['n nat]]
                  (induct claim
                          (f/lam [['H (hyp nz)]] (f/const* 'proposition/trivial []))
                          (fn [q ih]
                            (f/lam [['H (hyp (succ q))]]
                                   (list-law 'signed/all-at-most-cons 'F 'G q (indices q)
                                             (at 'H q (self-below q))
                                             (at ih (f/lam [['idx nat] ['bound (below 'idx q)]]
                                                           (at 'H 'idx (weaken 'idx q 'bound))))))) 'n))}))

(def monotone-spec
  (spec 'signed/expr-sum-value-monotone-below
        [['F family] ['G family] ['n nat]
         ['H (all-below 'n #(le (at 'F %) (at 'G %)))]]
        (le (sum 'F 'n) (sum 'G 'n))
        (le-transport (map-sum 'F 'n) (sum 'F 'n) (map-sum 'G 'n) (sum 'G 'n)
                      (sym (sum 'F 'n) (map-sum 'F 'n) (bridge 'F 'n))
                      (sym (sum 'G 'n) (map-sum 'G 'n) (bridge 'G 'n))
                      (list-law 'signed/map-sum-monotone-on 'F 'G (indices 'n)
                                (call 'signed/expr-sum-bounds-as-list 'F 'G 'n 'H)))))

(def respects-spec
  (spec 'signed/expr-sum-value-respects-equivalence-below
        [['F family] ['G family] ['n nat]
         ['H (all-below 'n #(eqv (at 'F %) (at 'G %)))]]
        (eqv (sum 'F 'n) (sum 'G 'n))
        (call 'signed/at-most-antisymmetric (sum 'F 'n) (sum 'G 'n)
              (call 'signed/expr-sum-value-monotone-below 'F 'G 'n
                    (f/lam [['idx nat] ['bound (below 'idx 'n)]]
                           (call 'signed/equivalent-to-at-most (at 'F 'idx) (at 'G 'idx) (at 'H 'idx 'bound))))
              (call 'signed/expr-sum-value-monotone-below 'G 'F 'n
                    (f/lam [['idx nat] ['bound (below 'idx 'n)]]
                           (call 'signed/equivalent-to-at-most (at 'G 'idx) (at 'F 'idx)
                                 (sym (at 'F 'idx) (at 'G 'idx) (at 'H 'idx 'bound))))))))

(defn sum-cong [g h n proof]
  (call 'signed/expr-sum-value-respects-equivalence-below g h n proof))

(def scale-left-spec
  (let [g (f/lam [['i nat]] (mul (at 'F 'i) 'c))
        h (f/lam [['i nat]] (mul 'c (at 'F 'i))) a (sum 'F 'n)]
    (spec 'signed/expr-sum-value-scale-left [['F family] ['c signed] ['n nat]]
          (eqv (mul 'c a) (sum h 'n))
          (trans (mul 'c a) (mul a 'c) (sum h 'n)
                 (call 'signed/multiply-commutative 'c a)
                 (trans (mul a 'c) (sum g 'n) (sum h 'n)
                        (call 'signed/expr-sum-value-scale-right 'F 'c 'n)
                        (sum-cong g h 'n (f/lam [['idx nat] ['bound (below 'idx 'n)]]
                                                (call 'signed/multiply-commutative (at 'F 'idx) 'c))))))))

(defn- weighted-spec [name left?]
  (let [product (fn [v] (f/lam [['i nat]] (if left? (mul (at 'W 'i) (at v 'i)) (mul (at v 'i) (at 'W 'i)))))
        wf (product 'F) wg (product 'G)
        binders [['W family] ['F family] ['G family] ['n nat]
                 ['hw (all-below 'n #(le zero (at 'W %)))]
                 ['hfg (all-below 'n #(le (at 'F %) (at 'G %)))]]]
    (spec name binders (le (sum wf 'n) (sum wg 'n))
          (call 'signed/expr-sum-value-monotone-below wf wg 'n
                (f/lam [['idx nat] ['bound (below 'idx 'n)]]
                       (call (if left? 'signed/multiply-left-monotone 'signed/multiply-right-monotone)
                             (at 'W 'idx) (at 'F 'idx) (at 'G 'idx)
                             (at 'hw 'idx 'bound) (at 'hfg 'idx 'bound)))))))
(def weighted-left-spec (weighted-spec 'signed/expr-sum-value-weighted-monotone-left true))
(def weighted-right-spec (weighted-spec 'signed/expr-sum-value-weighted-monotone-right false))

(defn- nested-bridge [matrix inner outer]
  (let [row (fn [i] (f/lam [['j nat]] (at matrix i 'j)))
        sf (f/lam [['i nat]] (sum (row 'i) inner))
        lf (f/lam [['i nat]] (map-sum (row 'i) inner))]
    (trans (sum sf outer) (map-sum sf outer) (map-sum lf outer)
           (bridge sf outer)
           (list-law 'signed/map-sum-respects-equivalence sf lf
                     (f/lam [['i nat]] (bridge (row 'i) inner)) (indices outer)))))

(def swap-spec
  (let [T 'F Tr (f/lam [['j nat] ['i nat]] (at T 'i 'j))
        row (fn [i] (f/lam [['j nat]] (at T i 'j)))
        col (fn [j] (f/lam [['i nat]] (at T 'i j)))
        a (sum (f/lam [['i nat]] (sum (row 'i) 'n)) 'm)
        b (map-sum (f/lam [['i nat]] (map-sum (row 'i) 'n)) 'm)
        c (map-sum (f/lam [['j nat]] (map-sum (col 'j) 'm)) 'n)
        d (sum (f/lam [['j nat]] (sum (col 'j) 'm)) 'n)]
    (spec 'signed/expr-sum-value-swap [['F (f/arrow nat family)] ['n nat] ['m nat]] (eqv a d)
          (trans a b d (nested-bridge T 'n 'm)
                 (trans b c d
                        (f/app (f/const* 'signed/map-sum-swap [[:zero]])
                               nat nat T (indices 'm) (indices 'n))
                        (sym d c (nested-bridge Tr 'm 'n)))))))

(def theorem-specs [bridge-spec bounds-bridge-spec zero-spec add-spec scale-right-spec monotone-spec respects-spec
                    scale-left-spec weighted-left-spec weighted-right-spec swap-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.checks rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.distributive rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.signed.fubini rainbow.math.rational.signed.pointwise-order])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/add-spec-shared :finset-range ranges/nat-range-spec) (support/extend-with :expr-sum-value-algebra theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.value-algebra))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
