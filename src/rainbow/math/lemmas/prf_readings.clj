(ns rainbow.math.lemmas.prf-readings
  "General lemmas: prf readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.lemmas.pcmax-lower-bound :as pdep0]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.strict-order :as strict]
            [rainbow.math.checks :as combinators]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn ring [x y] (a/ring-eq x y))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn from-diff [x y h]
  (a/chain x [(add x s/zero) (ring x (add x s/zero))]
           [(add x (sub y x)) (s/add-cong x x s/zero (sub y x) (refl x) (sym (sub y x) s/zero h))]
           [y (ring (add x (sub y x)) y)]))

(defn diff-nn [x y h] (le-resp (sub x x) s/zero (sub y x) (sub y x) (ring (sub x x) s/zero) (refl (sub y x)) (call 'signed/add-right-monotone x y (neg x) h)))

(defn nn-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (ring (mul p s/zero) s/zero) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(def bool (f/const* 'data/Bool []))

(defn sel [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn pp "the checker's max(0, v): if-at-most 0 v v 0" [v] (sel s/zero v (call 'signed/decide-at-most s/zero v)))

(defn pp-facts [v w] (pconj (le s/zero w) (pconj (le v w) (disj (eqv w s/zero) (eqv w v)))))

(defn eq-le [x y h] (a/eq-le x y h))

(defn pfacts [v w] (pconj (disj (eqv w s/zero) (eqv w v)) (pconj (le s/zero w) (le v w))))

(defn mcong [x xh y yh h k] (call 'signed/multiply-respects-equivalence x xh y yh h k))

(defn acong [x xh y yh h k] (call 'signed/add-respects-equivalence x xh y yh h k))

(defn ring-atoms
  "ring-eq on x ~ y over fresh atoms, applied back to the given terms: [[atom term] ...] (ring-eq's proof
  size explodes with the number of atoms and their degree, so every rearrangement here is over <= 4 atoms)"
  [pairs x y]
  (reduce (fn [t [_ term]] (f/app t term)) (f/lam (mapv (fn [[v _]] [v signed]) pairs) (ring x y)) pairs))

(defn dl [k x y] (call 'signed/multiply-distributes-add-left k x y))

(defn dr [x y m] (call 'signed/multiply-distributes-add-right x y m))

(defn neg-mul [x y] (ring-atoms [['nm-x x] ['nm-y y]] (mul (neg 'nm-x) 'nm-y) (neg (mul 'nm-x 'nm-y))))

(defn mul-neg [x y] (ring-atoms [['mn-x x] ['mn-y y]] (mul 'mn-x (neg 'mn-y)) (neg (mul 'mn-x 'mn-y))))

(defn negc [x y h] (call 'signed/negate-respects-equivalence x y h))

(defn chain "trans along terms ts with proofs hs (each ts_i ~ ts_i+1)" [ts hs]
  (if (= 2 (count ts)) (first hs)
      (trans (first ts) (second ts) (last ts) (first hs) (chain (rest ts) (rest hs)))))

(defn lt [x y] (call 'signed/less-than x y))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(def positive-spec
  (let [x 'po-x]
    (s/spec 'signed/positive-of-at-least-one [[x signed] ['po-h (le one x)]]
            (lt s/zero x)
            (call 'signed/less-than-intro s/zero x (call 'signed/at-most-transitive s/zero one x zero-le-one 'po-h)
                  (f/lam [['po-e (eqv s/zero x)]]
                         (call 'signed/one-not-at-most-zero (le-resp one one x s/zero (refl one) (sym s/zero x 'po-e) 'po-h)))))))

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(def two-eq
  (let [o1 (of-nat/of-nat (s/succ s/nz)) o0 (of-nat/of-nat s/nz)
        o1-one (chain [o1 (add o0 one) (add s/zero one) one]
                      [(call 'signed/of-nat-successor s/nz)
                       (acong o0 s/zero one one (refl s/zero) (refl one))
                       (ring (add s/zero one) one)])]
    (chain [two (add o1 one) (add one one)]
           [(call 'signed/of-nat-successor (s/succ s/nz)) (acong o1 one one one o1-one (refl one))])))

(defn twice [T] (chain [(mul two T) (mul (add one one) T) (add (mul one T) (mul one T)) (add T T)]
                        [(mcong two (add one one) T T two-eq (refl T)) (dr one one T)
                         (acong (mul one T) T (mul one T) T (call 'signed/multiply-one-left T) (call 'signed/multiply-one-left T))]))

(def f1-spec
  (let [[T FP FN P R F] '[fh-t fh-fp fh-fn fh-p fh-r fh-f]
        a (add T FP) b (add T FN) TT (mul T T) PR (mul P R)
        den (add (mul two T) (add FP FN))
        hden (chain [den (add (add T T) (add FP FN)) (add a b)]
                    [(acong (mul two T) (add T T) (add FP FN) (add FP FN) (twice T) (refl (add FP FN)))
                     (ring-atoms [['fd-t T] ['fd-p FP] ['fd-n FN]] (add (add 'fd-t 'fd-t) (add 'fd-p 'fd-n)) (add (add 'fd-t 'fd-p) (add 'fd-t 'fd-n)))])
        hF2 (chain [(mul F (add a b)) (mul F den) (mul two T) (add T T)]
                   [(mcong F F (add a b) den (refl F) (sym den (add a b) hden)) 'fh-hf (twice T)])
        ;; P (a b) ~ T b and R (a b) ~ T a
        Pab (chain [(mul P (mul a b)) (mul (mul P a) b) (mul T b)]
                   [(sym (mul (mul P a) b) (mul P (mul a b)) (call 'signed/multiply-associative P a b))
                    (mcong (mul P a) T b b 'fh-hp (refl b))])
        Rab (chain [(mul R (mul a b)) (mul R (mul b a)) (mul (mul R b) a) (mul T a)]
                   [(mcong R R (mul a b) (mul b a) (refl R) (call 'signed/multiply-commutative a b))
                    (sym (mul (mul R b) a) (mul R (mul b a)) (call 'signed/multiply-associative R b a))
                    (mcong (mul R b) T a a 'fh-hr (refl a))])
        X (mul F (add P R)) Y (add PR PR) ab (mul a b)
        ;; X ab ~ (T + T) T
        Tba (add (mul T b) (mul T a))
        hX (chain [(mul X ab) (mul F (mul (add P R) ab)) (mul F (add (mul P ab) (mul R ab))) (mul F Tba)
                   (mul F (mul (add a b) T)) (mul (mul F (add a b)) T) (mul (add T T) T)]
                  [(call 'signed/multiply-associative F (add P R) ab)
                   (mcong F F (mul (add P R) ab) (add (mul P ab) (mul R ab)) (refl F) (dr P R ab))
                   (mcong F F (add (mul P ab) (mul R ab)) Tba (refl F) (acong (mul P ab) (mul T b) (mul R ab) (mul T a) Pab Rab))
                   (mcong F F Tba (mul (add a b) T) (refl F)
                          (chain [Tba (add (mul T a) (mul T b)) (mul T (add a b)) (mul (add a b) T)]
                                 [(ring-atoms [['fb-x (mul T b)] ['fb-y (mul T a)]] (add 'fb-x 'fb-y) (add 'fb-y 'fb-x))
                                  (sym (mul T (add a b)) (add (mul T a) (mul T b)) (dl T a b))
                                  (call 'signed/multiply-commutative T (add a b))]))
                   (sym (mul (mul F (add a b)) T) (mul F (mul (add a b) T)) (call 'signed/multiply-associative F (add a b) T))
                   (mcong (mul F (add a b)) (add T T) T T hF2 (refl T))])
        ;; PR ab ~ T T
        hPR (chain [(mul PR ab) (mul P (mul R ab)) (mul P (mul T a)) (mul P (mul a T)) (mul (mul P a) T) TT]
                   [(call 'signed/multiply-associative P R ab)
                    (mcong P P (mul R ab) (mul T a) (refl P) Rab)
                    (mcong P P (mul T a) (mul a T) (refl P) (call 'signed/multiply-commutative T a))
                    (sym (mul (mul P a) T) (mul P (mul a T)) (call 'signed/multiply-associative P a T))
                    (mcong (mul P a) T T T 'fh-hp (refl T))])
        hY (chain [(mul Y ab) (add (mul PR ab) (mul PR ab)) (add TT TT)]
                  [(dr PR PR ab) (acong (mul PR ab) TT (mul PR ab) TT hPR hPR)])
        hXY (chain [(mul X ab) (mul (add T T) T) (add TT TT) (mul Y ab)]
                   [hX (dr T T T) (sym (mul Y ab) (add TT TT) hY)])
        pa (call 'signed/positive-of-at-least-one a 'fh-ha) pb (call 'signed/positive-of-at-least-one b 'fh-hb)
        ;; X (a b) ~ Y (a b)  ->  (X a) b ~ (Y a) b  ->  X a ~ Y a  ->  X ~ Y
        hXa (call 'signed/multiply-cancel-positive-right (mul X a) (mul Y a) b pb
                  (chain [(mul (mul X a) b) (mul X ab) (mul Y ab) (mul (mul Y a) b)]
                         [(call 'signed/multiply-associative X a b) hXY
                          (sym (mul (mul Y a) b) (mul Y ab) (call 'signed/multiply-associative Y a b))]))]
    (s/spec 'signed/f1-harmonic
            [[T signed] [FP signed] [FN signed] [P signed] [R signed] [F signed]
             ['fh-hp (eqv (mul P a) T)] ['fh-hr (eqv (mul R b) T)] ['fh-hf (eqv (mul F den) (mul two T))]
             ['fh-ha (le one a)] ['fh-hb (le one b)]]
            (eqv X Y)
            (call 'signed/multiply-cancel-positive-right X Y a pa hXa))))

(def split-spec
  (let [[y h] '[sp-y sp-h] yh (mul y h)
        c1 (chain [(add yh (mul (add one (neg y)) h)) (add yh (add (mul one h) (mul (neg y) h))) (add yh (add h (neg yh))) h]
                  [(acong yh yh (mul (add one (neg y)) h) (add (mul one h) (mul (neg y) h)) (refl yh) (dr one (neg y) h))
                   (acong yh yh (add (mul one h) (mul (neg y) h)) (add h (neg yh)) (refl yh)
                          (acong (mul one h) h (mul (neg y) h) (neg yh) (call 'signed/multiply-one-left h) (neg-mul y h)))
                   (ring-atoms [['sq-a yh] ['sq-h h]] (add 'sq-a (add 'sq-h (neg 'sq-a))) 'sq-h)])
        yone (trans (mul y one) (mul one y) y (call 'signed/multiply-commutative y one) (call 'signed/multiply-one-left y))
        c2 (chain [(add yh (mul y (add one (neg h)))) (add yh (add (mul y one) (mul y (neg h)))) (add yh (add y (neg yh))) y]
                  [(acong yh yh (mul y (add one (neg h))) (add (mul y one) (mul y (neg h))) (refl yh) (dl y one (neg h)))
                   (acong yh yh (add (mul y one) (mul y (neg h))) (add y (neg yh)) (refl yh)
                          (acong (mul y one) y (mul y (neg h)) (neg yh) yone (mul-neg y h)))
                   (ring-atoms [['sr-a yh] ['sr-y y]] (add 'sr-a (add 'sr-y (neg 'sr-a))) 'sr-y)])]
    (s/spec 'signed/indicator-cell-split [[y signed] [h signed]]
            (pconj (eqv (add yh (mul (add one (neg y)) h)) h) (eqv (add yh (mul y (add one (neg h)))) y))
            (conjoin (eqv (add yh (mul (add one (neg y)) h)) h) (eqv (add yh (mul y (add one (neg h)))) y) c1 c2))))

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

(def borrowed-specs [mmck/cancel-or-zero-spec mmck/cancel-positive-spec])

(def theorem-specs [positive-spec f1-spec split-spec])

(defn extend-environment [checked-environment]
  (-> (pdep0/extend-environment checked-environment)
      center/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      decide/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-order/extend-environment
      multiply-ring/extend-environment
      map-sum/extend-environment
      distributive/extend-environment
      unit-laws/extend-environment
      multiply-associative/extend-environment
      equivalence/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      of-nat/extend-environment
      strict/extend-environment
      combinators/extend-environment
      (support/extend-with-shared :expr-sum-prf-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
