(ns rainbow.math.lemmas.two-opt-local
  "General lemmas: two opt local. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed zero family call at sum add eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a :refer [nadd enat nr nsym nt nsubst nle nlt chain ring-eq]]
            [rainbow.math.nat.monus :as monus-module]
            [rainbow.algorithms.proofs.graph.walk-concat :as concat-module]))

(def walk (f/arrow nat nat))

(defn monus [x y] (call 'nat/monus x y))

(defn next-of [m i] (call 'nat/next-of m i))

(defn ncong [F x y h]
  (nsubst x y h (f/lam [['replacement nat]] (enat (F x) (F 'replacement))) (nr (F x))))

(defn n-equiv [F x y h]
  (nsubst x y h (f/lam [['replacement nat]] (eqv (F x) (F 'replacement))) (refl (F x))))

(defn rec-nat [claim base step n]
  (f/app (f/const* 'data/Nat.rec [[:zero]]) (f/lam [['n nat]] (claim 'n)) base
         (f/lam [['n nat] ['ih (claim 'n)]] (step 'n 'ih)) n))

(defn with-gap [lo hi h tag goal body]
  (let [d (symbol (str tag "-gap")) hd (symbol (str tag "-equality"))]
    (at h goal (f/lam [[d nat] [hd (enat (nadd lo d) hi)]] (body d hd)))))

(def monus-successor-spec
  (let [claim (fn [n i] (enat (monus (s/succ n) i) (s/succ (monus n i))))]
    (s/spec 'nat/monus-successor-left-below
            [['n nat] ['i nat] ['below (nle 'i 'n)]] (claim 'n 'i)
            (with-gap 'i 'n 'below "difference" (claim 'n 'i)
              (fn [d hd]
                (let [total (nadd 'i d) left (monus (s/succ total) 'i)
                      padded (monus (nadd 'i (s/succ d)) 'i)
                      inner (monus total 'i)
                      h1 (ncong #(monus % 'i) (s/succ total) (nadd 'i (s/succ d))
                                (nsym (nadd 'i (s/succ d)) (s/succ total)
                                      (call 'nat/add-successor-right 'i d)))
                      h2 (call 'nat/monus-add-cancel-left 'i (s/succ d))
                      h3 (ncong s/succ d inner (nsym inner d (call 'nat/monus-add-cancel-left 'i d)))
                      proof (nt left padded (s/succ inner) h1 (nt padded (s/succ d) (s/succ inner) h2 h3))]
                  (nsubst total 'n hd (f/lam [['size nat]] (claim 'size 'i)) proof)))))))

(def monus-self-spec
  (let [claim #(enat (monus % %) s/nz)]
    (s/spec 'nat/monus-self-zero [['n nat]] (claim 'n)
            (rec-nat claim (nr s/nz) (fn [_ ih] ih) 'n))))

(def reverse-sum-spec
  (let [rev (fn [n] (f/lam [['ri nat]] (at 'F (monus n 'ri))))
        claim #(eqv (sum (rev %) (s/succ %)) (sum 'F (s/succ %)))]
    (s/spec 'signed/expr-sum-value-reverse [['F family] ['n nat]] (claim 'n)
            (rec-nat claim (refl (sum 'F (s/succ s/nz)))
              (fn [n ih]
                (let [G (rev (s/succ n)) H (rev n) SF (sum 'F (s/succ n)) last (at 'F (s/succ n))]
                  (chain (sum G (s/succ (s/succ n)))
                         [(add last (sum H (s/succ n))) (call 'signed/expr-sum-value-head-tail G (s/succ n))]
                         [(add last SF) (s/add-cong last last (sum H (s/succ n)) SF (refl last) ih)]
                         [(sum 'F (s/succ (s/succ n))) (call 'signed/add-commutative last SF)]))) 'n))))

(defn reverse-walk [t k] (f/lam [['position nat]] (at t (monus k 'position))))

(defn shift-walk [t offset] (f/lam [['position nat]] (at t (nadd 'position offset))))

(defn edges [W t] (f/lam [['position nat]] (at W (at t 'position) (at t (s/succ 'position)))))

(defn walk-length [W t k] (sum (edges W t) k))

(defn symmetric-on [W t]
  (f/forall [['u nat] ['v nat]] (eqv (at W (at t 'u) (at t 'v)) (at W (at t 'v) (at t 'u)))))

(def reverse-walk-spec
  (let [W 'W t 't claim #(eqv (walk-length W (reverse-walk t %) %) (walk-length W t %))]
    (s/spec 'signed/symmetric-walk-reverse-length
            [['W a/matrix] ['t walk] ['symmetric (symmetric-on W t)] ['k nat]] (claim 'k)
            (rec-nat claim (refl zero)
              (fn [n _]
                (let [k (s/succ n) G (edges W (reverse-walk t k)) F (edges W t)
                      H (f/lam [['ri nat]] (at F (monus n 'ri)))
                      same (a/sum-cong G H k 'i
                             (fn [i hi]
                               (let [d (monus n i) first-index (monus k i)
                                     h (call 'nat/monus-successor-left-below n i
                                             (call 'nat/at-most-add-left-cancel i n (s/succ s/nz) hi))
                                     term #(at W (at t %) (at t d))]
                                 (chain (at G i)
                                        [(term (s/succ d)) (n-equiv term first-index (s/succ d) h)]
                                        [(at H i) (at 'symmetric (s/succ d) d)]))))]
                  (chain (sum G k) [(sum H k) same]
                         [(sum F k) (call 'signed/expr-sum-value-reverse F n)]))) 'k))))

(defn prepend [v t]
  (f/lam [['position nat]]
         (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]]) (f/lam [['ignored nat]] nat) v
                (f/lam [['previous nat] ['ignored nat]] (at t 'previous)) 'position)))

(def prepend-spec
  (s/spec 'signed/walk-prepend-length [['W a/matrix] ['v nat] ['t walk] ['k nat]]
          (eqv (walk-length 'W (prepend 'v 't) (s/succ 'k))
               (add (at 'W 'v (at 't s/nz)) (walk-length 'W 't 'k)))
          (call 'signed/expr-sum-value-head-tail (edges 'W (prepend 'v 't)) 'k)))

(def split-spec
  (s/spec 'signed/walk-length-split [['W a/matrix] ['t walk] ['a nat] ['b nat]]
          (eqv (walk-length 'W 't (nadd 'b 'a))
               (add (walk-length 'W 't 'a) (walk-length 'W (shift-walk 't 'a) 'b)))
          (call 'signed/expr-sum-value-append (edges 'W 't) 'a 'b)))

(defn closed-index [m i]
  (f/app (f/const* 'data/Nat.rec [[:succ [:zero]]]) (f/lam [['ignored nat]] nat) s/nz
         (f/lam [['previous nat] ['ignored nat]] (next-of m 'previous)) i))

(defn closed-walk [t m] (f/lam [['position nat]] (at t (closed-index m 'position))))

(defn tour-length
  "The unchanged expr-sum-value of the m wraparound tour edges."
  [W t m]
  (sum (f/lam [['position nat]] (at W (at t 'position) (at t (next-of m 'position)))) m))

(def bool (f/const* 'data/Bool []))

(def bt (f/const* 'data/true []))

(def bf (f/const* 'data/false []))

(defn bsubst [x y h P v]
  (f/app (f/const* 'equality/substitution [[:succ [:zero]]]) bool x y h P v))

(defn bsym [x y h]
  (f/app (f/const* 'equality/symmetric [[:succ [:zero]]]) bool x y h))

(defn choose-nat [no yes test]
  (f/app (f/const* 'data/Bool.rec [[:succ [:zero]]]) (f/lam [['ignored bool]] nat) no yes test))

(defn next-proof [m i test result h]
  (let [decision (call 'nat/decide-at-most (s/succ (s/succ i)) m)]
    (bsubst test decision (bsym decision test h)
            (f/lam [['decision-result bool]]
                   (enat (choose-nat s/nz (s/succ i) 'decision-result) result)) (nr result))))

(def next-interior-spec
  (s/spec 'nat/two-opt-next-interior [['m nat] ['i nat] ['inside (nlt (s/succ 'i) 'm)]]
          (enat (next-of 'm 'i) (s/succ 'i))
          (next-proof 'm 'i bt (s/succ 'i)
                      (call 'nat/decide-at-most-true-complete (s/succ (s/succ 'i)) 'm 'inside))))

(def next-last-spec
  (s/spec 'nat/two-opt-next-last [['i nat]] (enat (next-of (s/succ 'i) 'i) s/nz)
          (next-proof (s/succ 'i) 'i bf s/nz
                      (call 'nat/decide-at-most-false-complete (s/succ (s/succ 'i)) (s/succ 'i)
                            (call 'nat/not-strictly-below-self (s/succ 'i))))))

(def closed-below-spec
  (let [claim #(f/forall [['inside (nlt % 'm)]] (enat (closed-index 'm %) %))]
    (s/spec 'nat/two-opt-closed-index-below [['m nat] ['i nat]] (claim 'i)
            (rec-nat claim (f/lam [['inside (nlt s/nz 'm)]] (nr s/nz))
                     (fn [n _] (f/lam [['inside (nlt (s/succ n) 'm)]]
                                      (call 'nat/two-opt-next-interior 'm n 'inside))) 'i))))

(def closed-end-spec
  (let [claim #(enat (closed-index % %) s/nz)]
    (s/spec 'nat/two-opt-closed-index-end [['m nat]] (claim 'm)
            (rec-nat claim (nr s/nz) (fn [n _] (call 'nat/two-opt-next-last n)) 'm))))

(def closed-length-spec
  (s/spec 'signed/two-opt-closed-walk-length [['W a/matrix] ['t walk] ['m nat]]
          (eqv (walk-length 'W (closed-walk 't 'm) 'm) (tour-length 'W 't 'm))
          (a/sum-cong (edges 'W (closed-walk 't 'm))
                      (f/lam [['position nat]] (at 'W (at 't 'position) (at 't (next-of 'm 'position))))
                      'm 'i
                      (fn [i hi]
                        (n-equiv #(at 'W (at 't %) (at 't (next-of 'm i)))
                                 (closed-index 'm i) i (call 'nat/two-opt-closed-index-below 'm i hi))))))

(def closed-tour-length-spec
  (let [claim (eqv (tour-length 'W 't 'm) (walk-length 'W 't 'm))]
    (s/spec 'signed/two-opt-closed-tour-length
            [['W a/matrix] ['t walk] ['m nat] ['closed (enat (at 't 'm) (at 't s/nz))]] claim
            (a/sum-cong
             (f/lam [['position nat]] (at 'W (at 't 'position) (at 't (next-of 'm 'position))))
             (edges 'W 't) 'm 'i
             (fn [i hi]
               (let [si (s/succ i) P (enat si 'm) Q (nlt si 'm)
                     F #(at 'W (at 't i) (at 't %))
                     goal (eqv (F (next-of 'm i)) (F si))
                     last-next (nsubst si 'm 'last-index
                                       (f/lam [['size nat]] (enat (next-of 'size i) s/nz))
                                       (call 'nat/two-opt-next-last i))
                     t-end (nt (at 't si) (at 't 'm) (at 't s/nz)
                               (ncong #(at 't %) si 'm 'last-index) 'closed)]
                 (a/cases P Q goal (call 'nat/at-most-split si 'm hi)
                          (f/lam [['last-index P]]
                                 (chain (F (next-of 'm i))
                                        [(F s/nz) (n-equiv F (next-of 'm i) s/nz last-next)]
                                        [(F si) (n-equiv #(at 'W (at 't i) %) (at 't s/nz) (at 't si)
                                                         (nsym (at 't si) (at 't s/nz) t-end))]))
                          (f/lam [['interior Q]]
                                 (n-equiv F (next-of 'm i) si
                                          (call 'nat/two-opt-next-interior 'm i 'interior))))))))))

(def shifted-head-spec
  (let [T (shift-walk 't 'a) U (shift-walk 't (s/succ 'a))
        G (f/lam [['position nat]] (at (edges 'W T) (s/succ 'position)))]
    (s/spec 'signed/walk-shift-head-tail [['W a/matrix] ['t walk] ['a nat] ['k nat]]
            (eqv (walk-length 'W T (s/succ 'k))
                 (add (at 'W (at 't 'a) (at 't (s/succ 'a))) (walk-length 'W U 'k)))
            (let [head (at 'W (at 't 'a) (at 't (s/succ 'a)))
                  h (a/sum-cong G (edges 'W U) 'k 'i
                                (fn [i _]
                                  (n-equiv #(at 'W (at 't %) (at 't (s/succ %)))
                                           (s/succ (nadd i 'a)) (nadd i (s/succ 'a))
                                           (nsym (nadd i (s/succ 'a)) (s/succ (nadd i 'a))
                                                 (call 'nat/add-successor-right i 'a)))))]
              (chain (walk-length 'W T (s/succ 'k))
                     [(add head (sum G 'k)) (call 'signed/expr-sum-value-head-tail (edges 'W T) 'k)]
                     [(add head (walk-length 'W U 'k))
                      (s/add-cong head head (sum G 'k) (walk-length 'W U 'k) (refl head) h)])))))

(defn join-walk [x a y]
  (f/lam [['joined-position nat]]
         (choose-nat (at y (monus 'joined-position a)) (at x 'joined-position)
                     (call 'nat/decide-at-most 'joined-position a))))

(defn conjunction [P Q] (call 'proposition/conjunction P Q))

(defn first-proof [P Q h] (at h P (f/lam [['conj-left P] ['conj-right Q]] 'conj-left)))

(defn second-proof [P Q h] (at h Q (f/lam [['conj-left P] ['conj-right Q]] 'conj-right)))

(defn concat-facts [W x a y b join]
  (let [z (join-walk x a y)
        P (enat (at z s/nz) (at x s/nz))
        Q (enat (at z (nadd b a)) (at y b))
        L (eqv (walk-length W z (nadd b a)) (add (walk-length W x a) (walk-length W y b)))
        h (call 'signed/walk-concat W x a y b join)
        tail (second-proof P (conjunction Q L) h)]
    {:walk z :start (first-proof P (conjunction Q L) h)
     :end (first-proof Q L tail) :length (second-proof Q L tail)}))

(defn block-reversal
  "Keep positions through a, reverse the next b+1 nodes, then keep the suffix.
  This constructs node indices; it never refers to costs or delta."
  [t a b]
  (let [j (nadd (s/succ b) a)
        Q (prepend (at t a) (reverse-walk (shift-walk t (s/succ a)) b))
        T (prepend (at t (s/succ a)) (shift-walk t (s/succ j)))]
    (join-walk (join-walk t a Q) j T)))

(defn block-delta [W t a j]
  (a/sub (add (at W (at t a) (at t (s/succ a))) (at W (at t j) (at t (s/succ j))))
         (add (at W (at t a) (at t j)) (at W (at t (s/succ a)) (at t (s/succ j))))))

(defn block-data [W t symmetric a b c]
  (let [j (nadd (s/succ b) a) m (nadd (s/succ c) j)
        mid (shift-walk t (s/succ a)) rev (reverse-walk mid b)
        suf (shift-walk t (s/succ j))
        Q (prepend (at t a) rev) T (prepend (at t (s/succ a)) suf)
        f1 (concat-facts W t a Q (s/succ b) (nr (at t a)))
        rev-end (ncong #(at mid %) (monus b b) s/nz (call 'nat/monus-self-zero b))
        join (nt (at (:walk f1) j) (at rev b) (at t (s/succ a)) (:end f1) rev-end)
        f2 (concat-facts W (:walk f1) j T (s/succ c) join)
        endpoint (ncong #(at t %) (nadd c (s/succ j)) m (call 'nat/add-successor-right c j))
        end (nt (at (:walk f2) m) (at suf c) (at t m) (:end f2) endpoint)
        start (nt (at (:walk f2) s/nz) (at (:walk f1) s/nz) (at t s/nz) (:start f2) (:start f1))
        rev-start (nt (at rev s/nz) (at mid b) (at t j)
                      (ncong #(at mid %) (monus b s/nz) b (call 'nat/monus-zero-right b))
                      (ncong #(at t %) (nadd b (s/succ a)) j (call 'nat/add-successor-right b a)))
        rev-len (call 'signed/symmetric-walk-reverse-length W mid
                      (f/lam [['u nat] ['v nat]] (at symmetric (nadd 'u (s/succ a)) (nadd 'v (s/succ a)))) b)
        A (walk-length W t a) B (walk-length W mid b) C (walk-length W suf c)
        old1 (at W (at t a) (at t (s/succ a))) old2 (at W (at t j) (at t (s/succ j)))
        new1 (at W (at t a) (at t j)) new2 (at W (at t (s/succ a)) (at t (s/succ j)))
        qnormal (add new1 B) tnormal (add new2 C)
        qlen (chain (walk-length W Q (s/succ b))
                    [(add (at W (at t a) (at rev s/nz)) (walk-length W rev b))
                     (call 'signed/walk-prepend-length W (at t a) rev b)]
                    [qnormal (s/add-cong (at W (at t a) (at rev s/nz)) new1 (walk-length W rev b) B
                                        (n-equiv #(at W (at t a) %) (at rev s/nz) (at t j) rev-start) rev-len)])
        tlen (call 'signed/walk-prepend-length W (at t (s/succ a)) suf c)
        first-normal (add A qnormal)
        first-len (chain (walk-length W (:walk f1) j)
                         [(add A (walk-length W Q (s/succ b))) (:length f1)]
                         [first-normal (s/add-cong A A (walk-length W Q (s/succ b)) qnormal (refl A) qlen)])
        new-normal (add first-normal tnormal)
        new-len (chain (walk-length W (:walk f2) m)
                       [(add (walk-length W (:walk f1) j) (walk-length W T (s/succ c))) (:length f2)]
                       [new-normal (s/add-cong (walk-length W (:walk f1) j) first-normal
                                              (walk-length W T (s/succ c)) tnormal first-len tlen)])
        old-first (add A (add old1 B)) old-normal (add old-first (add old2 C))
        old-pre (chain (walk-length W t j)
                       [(add A (walk-length W (shift-walk t a) (s/succ b)))
                        (call 'signed/walk-length-split W t a (s/succ b))]
                       [old-first (s/add-cong A A (walk-length W (shift-walk t a) (s/succ b)) (add old1 B)
                                             (refl A) (call 'signed/walk-shift-head-tail W t a b))])
        old-len (chain (walk-length W t m)
                       [(add (walk-length W t j) (walk-length W (shift-walk t j) (s/succ c)))
                        (call 'signed/walk-length-split W t j (s/succ c))]
                       [old-normal (s/add-cong (walk-length W t j) old-first
                                              (walk-length W (shift-walk t j) (s/succ c)) (add old2 C)
                                              old-pre (call 'signed/walk-shift-head-tail W t j c))])
        delta (block-delta W t a j)
        length-proof (chain (walk-length W (:walk f2) m)
                            [new-normal new-len]
                            [(a/sub old-normal delta) (ring-eq new-normal (a/sub old-normal delta))]
                            [(a/sub (walk-length W t m) delta)
                             (s/add-cong old-normal (walk-length W t m) (a/neg delta) (a/neg delta)
                                         (sym (walk-length W t m) old-normal old-len) (refl (a/neg delta)))])]
    {:walk (:walk f2) :m m :j j :start start :end end :length length-proof}))

(def block-length-spec
  (let [j (nadd (s/succ 'b) 'a) m (nadd (s/succ 'c) j)]
    (s/spec 'signed/two-opt-block-length
            [['W a/matrix] ['t walk] ['symmetric (symmetric-on 'W 't)] ['a nat] ['b nat] ['c nat]]
            (eqv (walk-length 'W (block-reversal 't 'a 'b) m)
                 (a/sub (walk-length 'W 't m) (block-delta 'W 't 'a j)))
            (:length (block-data 'W 't 'symmetric 'a 'b 'c)))))

(def block-start-spec
  (s/spec 'nat/two-opt-block-start [['t walk] ['a nat] ['b nat]]
          (enat (at (block-reversal 't 'a 'b) s/nz) (at 't s/nz))
          (:start (block-data (f/lam [['u nat] ['v nat]] zero) 't
                              (f/lam [['u nat] ['v nat]] (refl zero)) 'a 'b s/nz))))

(def block-end-spec
  (let [m (nadd (s/succ 'c) (nadd (s/succ 'b) 'a))]
    (s/spec 'nat/two-opt-block-end [['t walk] ['a nat] ['b nat] ['c nat]]
            (enat (at (block-reversal 't 'a 'b) m) (at 't m))
            (:end (block-data (f/lam [['u nat] ['v nat]] zero) 't
                              (f/lam [['u nat] ['v nat]] (refl zero)) 'a 'b 'c)))))

(defn witness-gap [lo hi gap proof]
  (f/app (f/const* 'proposition/witness [[:succ [:zero]]]) nat
         (f/lam [['difference nat]] (enat (nadd lo 'difference) hi)) gap proof))

(defn count-below [a b]
  (witness-gap (s/succ a) (nadd (s/succ b) a) b
               (ncong s/succ (nadd a b) (nadd b a) (call 'nat/add-commutative a b))))

(defn reverse-tour
  "For i<j<m, reverse positions i+1..j, including j=m-1. Close the walk
  at m before concatenation so its final edge returns to the original start."
  [t m i j]
  (block-reversal (closed-walk t m) i (monus j (s/succ i))))

(defn tour-delta [W t m i j]
  (a/sub (add (at W (at t i) (at t (next-of m i))) (at W (at t j) (at t (next-of m j))))
         (add (at W (at t i) (at t j)) (at W (at t (next-of m i)) (at t (next-of m j))))))

(defn tour-reversal-claim [W t m i j]
  (eqv (tour-length W (reverse-tour t m i j) m)
       (a/sub (tour-length W t m) (tour-delta W t m i j))))

(def counted-tour-spec
  (let [W 'W t 't a 'a b 'b c 'c j (nadd (s/succ b) a) m (nadd (s/succ c) j)
        F (closed-walk t m) R (block-reversal F a b)
        bcalc (monus j (s/succ a))
        bproof (nt bcalc (monus (nadd b (s/succ a)) (s/succ a)) b
                   (ncong #(monus % (s/succ a)) j (nadd b (s/succ a))
                          (nsym (nadd b (s/succ a)) j (call 'nat/add-successor-right b a)))
                   (call 'nat/monus-after-add b (s/succ a)))
        closed (nt (at R m) (at F m) (at R s/nz)
                   (call 'nat/two-opt-block-end F a b c)
                   (nt (at F m) (at F s/nz) (at R s/nz)
                       (ncong #(at t %) (closed-index m m) s/nz (call 'nat/two-opt-closed-index-end m))
                       (nsym (at R s/nz) (at F s/nz) (call 'nat/two-opt-block-start F a b))))
        hij (count-below a b) hjm (count-below j c)
        him (a/ntrans (s/succ a) j m hij
                      (a/ntrans j (s/succ j) m (call 'nat/at-most-successor j) hjm))
        ha (ncong #(at t %) (closed-index m a) a (call 'nat/two-opt-closed-index-below m a him))
        hj (ncong #(at t %) (closed-index m j) j (call 'nat/two-opt-closed-index-below m j hjm))
        A (at W (at F a) (at F (s/succ a))) A2 (at W (at t a) (at t (next-of m a)))
        B (at W (at F j) (at F (s/succ j))) B2 (at W (at t j) (at t (next-of m j)))
        C (at W (at F a) (at F j)) C2 (at W (at t a) (at t j))
        D (at W (at F (s/succ a)) (at F (s/succ j)))
        ah (n-equiv #(at W % (at F (s/succ a))) (at F a) (at t a) ha)
        bh (n-equiv #(at W % (at F (s/succ j))) (at F j) (at t j) hj)
        ch (chain C
                  [(at W (at t a) (at F j)) (n-equiv #(at W % (at F j)) (at F a) (at t a) ha)]
                  [C2 (n-equiv #(at W (at t a) %) (at F j) (at t j) hj)])
        delta (block-delta W F a j) delta2 (tour-delta W t m a j)
        dh (s/add-cong (add A B) (add A2 B2) (a/neg (add C D)) (a/neg (add C2 D))
                       (s/add-cong A A2 B B2 ah bh)
                       (a/neg-cong (add C D) (add C2 D) (s/add-cong C C2 D D ch (refl D))))
        lenh (call 'signed/two-opt-closed-walk-length W t m)
        symF (f/lam [['u nat] ['v nat]] (at 'symmetric (closed-index m 'u) (closed-index m 'v)))]
    (s/spec 'signed/two-opt-counted-tour-length
            [['W a/matrix] ['t walk] ['symmetric (symmetric-on W t)] ['a nat] ['b nat] ['c nat]]
            (tour-reversal-claim W t m a j)
            (chain (tour-length W (reverse-tour t m a j) m)
                   [(tour-length W R m) (n-equiv #(tour-length W (block-reversal F a %) m) bcalc b bproof)]
                   [(walk-length W R m) (call 'signed/two-opt-closed-tour-length W R m closed)]
                   [(a/sub (walk-length W F m) delta) (call 'signed/two-opt-block-length W F symF a b c)]
                   [(a/sub (tour-length W t m) delta2)
                    (s/add-cong (walk-length W F m) (tour-length W t m) (a/neg delta) (a/neg delta2)
                                lenh (a/neg-cong delta delta2 dh))]))))

(def tour-reversal-spec
  (s/spec 'signed/two-opt-tour-length
          [['W a/matrix] ['t walk] ['symmetric (symmetric-on 'W 't)] ['m nat] ['i nat] ['j nat]
           ['ordered (nlt 'i 'j)] ['bounded (nlt 'j 'm)]]
          (tour-reversal-claim 'W 't 'm 'i 'j)
          (with-gap (s/succ 'i) 'j 'ordered "middle" (tour-reversal-claim 'W 't 'm 'i 'j)
            (fn [b hb]
              (with-gap (s/succ 'j) 'm 'bounded "suffix" (tour-reversal-claim 'W 't 'm 'i 'j)
                (fn [c hc]
                  (let [jj (nadd (s/succ b) 'i) mm (nadd (s/succ c) jj)
                        jm (nadd (s/succ c) 'j)
                        heqj (nt jj (nadd (s/succ 'i) b) 'j
                                  (ncong s/succ (nadd b 'i) (nadd 'i b) (call 'nat/add-commutative b 'i)) hb)
                        heqm (nt jm (nadd (s/succ 'j) c) 'm
                                  (ncong s/succ (nadd c 'j) (nadd 'j c) (call 'nat/add-commutative c 'j)) hc)
                        raw (call 'signed/two-opt-counted-tour-length 'W 't 'symmetric 'i b c)
                        jdone (nsubst jj 'j heqj
                                      (f/lam [['last-cut nat]] (tour-reversal-claim 'W 't (nadd (s/succ c) 'last-cut) 'i 'last-cut)) raw)]
                    (nsubst jm 'm heqm (f/lam [['size nat]] (tour-reversal-claim 'W 't 'size 'i 'j)) jdone))))))))

(def pair-binders [['i nat] ['j nat] ['ordered (nlt 'i 'j)] ['bounded (nlt 'j 'm)]])

(defn nonshorter [W t m i j] (s/le (tour-length W t m) (tour-length W (reverse-tour t m i j) m)))

(defn gain-length-proof [W t symmetric m i j hij hjm ordered converse?]
  (let [old (tour-length W t m) new (tour-length W (reverse-tour t m i j) m)
        d (tour-delta W t m i j)
        identity (call 'signed/two-opt-tour-length W t symmetric m i j hij hjm)
        gap (chain (add d new)
                   [(add d (a/sub old d)) (s/add-cong d d new (a/sub old d) (refl d) identity)]
                   [old (ring-eq (add d (a/sub old d)) old)])]
    (if converse?
      (let [h (call 'signed/add-right-monotone old new (a/neg new) ordered)
            lhs (a/sub old new) rhs (a/sub new new)
            same (chain lhs
                        [(a/sub (add d new) new)
                         (s/add-cong old (add d new) (a/neg new) (a/neg new)
                                     (sym (add d new) old gap) (refl (a/neg new)))]
                        [d (ring-eq (a/sub (add d new) new) d)])]
        (s/le-transport lhs d rhs zero same (ring-eq rhs zero) h))
      (s/le-transport (add d new) old (add zero new) new gap (ring-eq (add zero new) new)
                      (call 'signed/add-right-monotone d zero new ordered)))))

(defn gain-length-spec [converse? name]
  (let [base [['W a/matrix] ['t walk] ['symmetric (symmetric-on 'W 't)] ['m nat]]
        gain (s/le (tour-delta 'W 't 'm 'i 'j) zero)
        length (nonshorter 'W 't 'm 'i 'j)]
    (s/spec name (into (into base pair-binders) [['hypothesis (if converse? length gain)]])
            (if converse? gain length)
            (gain-length-proof 'W 't 'symmetric 'm 'i 'j 'ordered 'bounded 'hypothesis converse?))))

(def gain-to-length-spec (gain-length-spec false 'signed/two-opt-nonpositive-gain-nonshorter))

(def length-to-gain-spec (gain-length-spec true 'signed/two-opt-nonshorter-nonpositive-gain))

(defn matrix-value [env m] (f/lam [['city-a nat] ['city-b nat]] (at env (nadd 'city-b (a/nmul 'city-a m)))))

(defn matrix-symmetric [env m]
  (f/forall [['city-a nat] ['a-below (nlt 'city-a m)] ['city-b nat] ['b-below (nlt 'city-b m)]]
            (eqv (at env (nadd 'city-b (a/nmul 'city-a m)))
                 (at env (nadd 'city-a (a/nmul 'city-b m))))))

(defn tour-symmetric [t ht hsym]
  (f/lam [['u nat] ['v nat]] (at hsym (at t 'u) (at ht 'u) (at t 'v) (at ht 'v))))

(defn selected [d test]
  (f/app (f/const* 'data/Bool.rec [[:succ [:zero]]]) (f/lam [['ignored bool]] signed) zero d test))

(defn locally-optimal [env m t]
  (f/forall [['i nat] ['j nat] ['ordered (nlt 'i 'j)] ['bounded (nlt 'j m)]]
            (nonshorter (matrix-value env m) t m 'i 'j)))

(def theorem-specs [monus-successor-spec monus-self-spec reverse-sum-spec reverse-walk-spec prepend-spec split-spec next-interior-spec next-last-spec closed-below-spec closed-end-spec closed-length-spec closed-tour-length-spec shifted-head-spec block-length-spec block-start-spec block-end-spec counted-tour-spec tour-reversal-spec gain-to-length-spec length-to-gain-spec gain-length-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      monus-module/extend-environment
      concat-module/extend-environment
      (support/extend-with :expr-sum-two-opt-local theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
