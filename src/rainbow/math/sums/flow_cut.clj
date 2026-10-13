(ns rainbow.math.sums.flow-cut
  "General lemmas: flow cut. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed zero family call at sum add mul le eqv refl sym trans]]
            [rainbow.math.sums.value-append :as append]
            [rainbow.math.rational.signed.add-associative :as associative]
            [rainbow.math.rational.nnrat.ring :as ring]
            [rainbow.math.rational.nnrat.identities :as identities]
            [rainbow.math.rational.signed.multiply-nonzero :as nonzero]
            [rainbow.math.rational.signed.lp-objective-negate :as negate-sums]
            [rainbow.math.nat.pair-index-inverse :as pair-index]
            [rainbow.module :as module]))

(def one (f/const* 'signed/one []))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (add x (neg y)))

(defn nadd [x y] (call 'algebra/nat-add x y))

(defn nmul [x y] (call 'nat/multiply x y))

(defn enat [x y] (f/equality [:succ [:zero]] nat x y))

(defn nr [x] (f/app (f/const* 'equality/reflexive [[:succ [:zero]]]) nat x))

(defn nsym [a b h] (f/app (f/const* 'equality/symmetric [[:succ [:zero]]]) nat a b h))

(defn nt [a b c h k] (f/app (f/const* 'equality/transitive [[:succ [:zero]]]) nat a b c h k))

(defn nsubst [a b h P v] (f/app (f/const* 'equality/substitution [[:succ [:zero]]]) nat a b h P v))

(defn nle [a b] (call 'nat/at-most a b))

(defn nlt [a b] (s/below a b))

(defn ntrans [a b c h k] (call 'nat/at-most-transitive a b c h k))

(defn disj [P Q] (call 'proposition/disjunction P Q))

(defn cases [P Q R h p q] (call 'proposition/use-disjunction P Q R h p q))

(defn mul-cong [a b c d h k] (call 'signed/multiply-respects-equivalence a b c d h k))

(defn neg-cong [a b h] (call 'signed/negate-respects-equivalence a b h))

(defn eq-le [a b h] (call 'signed/equivalent-to-at-most a b h))

(defn le-trans [a b c h k] (call 'signed/at-most-transitive a b c h k))

(def rz (f/const* 'nnrat/zero []))

(def ro (f/const* 'nnrat/one []))

(defn components [v]
  (let [[tag head a b] (when (vector? v) v) name (when (and (= tag :app) (vector? head) (= :const (first head))) (second head))]
    (cond (= v zero) [rz rz] (= v one) [ro rz]
          (= name 'signed/negate) (vec (reverse (components a)))
          (= name 'signed/add) (mapv ring/radd (components a) (components b))
          (= name 'signed/multiply)
          (let [[p n] (components a) [q m] (components b)]
            [(ring/radd (ring/rmul p q) (ring/rmul n m))
             (ring/radd (ring/rmul p m) (ring/rmul n q))])
          :else [(call 'signed/positive v) (call 'signed/negative v)])))

(defn rat-simplify [v]
  (let [[tag head a b] (when (vector? v) v) op (when (and (= tag :app) (vector? head) (= :const (first head))) (second head))]
    (if (#{'nnrat/add 'nnrat/multiply} op)
      (let [[aa ha] (rat-simplify a) [bb hb] (rat-simplify b)
            mid (call op aa bb)
            cong (call (if (= op 'nnrat/add) 'nnrat/add-respects-equivalence 'nnrat/multiply-respects-equivalence)
                       a aa b bb ha hb)
            [out step]
            (if (= op 'nnrat/add)
              (cond (= aa rz) [bb (call 'nnrat/add-zero-left bb)]
                    (= bb rz) [aa (call 'nnrat/add-zero-right aa)]
                    :else [mid (call 'nnrat/equivalent-reflexive mid)])
              (cond (= aa rz) [rz (call 'nnrat/multiply-zero-left bb)]
                    (= bb rz) [rz (call 'nnrat/multiply-zero-right aa)]
                    (= aa ro) [bb (call 'nnrat/multiply-one-left bb)]
                    (= bb ro) [aa (call 'nnrat/multiply-one-right aa)]
                    :else [mid (call 'nnrat/equivalent-reflexive mid)]))]
        [out (call 'nnrat/equivalent-transitive v mid out cong step)])
      [v (call 'nnrat/equivalent-reflexive v)])))

(defn ring-eq [a b]
  (let [[ap an] (components a) [bp bn] (components b)
        l (ring/radd ap bn) r (ring/radd bp an)
        [ll hl] (rat-simplify l) [rr hr] (rat-simplify r)]
    (call 'nnrat/equivalent-transitive l ll r hl
          (call 'nnrat/equivalent-transitive ll rr r (ring/equiv ll rr)
                (call 'nnrat/equivalent-symmetric r rr hr)))))

(def flatten-spec
  (let [rows (f/lam [['i nat]] (sum (f/lam [['j nat]] (at 'F (nadd 'j (nmul 'i 'n)))) 'n))
        claim #(eqv (sum 'F (nmul % 'n)) (sum rows %))]
    (s/spec 'signed/expr-sum-value-rectangular [['F family] ['n nat] ['m nat]] (claim 'm)
            (s/induct claim (refl zero)
                      (fn [q ih]
                        (let [tail (sum (f/lam [['j nat]] (at 'F (nadd 'j (nmul q 'n)))) 'n)
                              a (sum 'F (nmul q 'n)) b (sum rows q)]
                          (trans (sum 'F (nmul (s/succ q) 'n)) (add a tail) (add b tail)
                                 (call 'signed/expr-sum-value-append 'F (nmul q 'n) 'n)
                                 (s/add-cong a b tail tail ih (refl tail))))) 'm))))

(def head-tail-spec
  (let [tail (f/lam [['i nat]] (at 'F (s/succ 'i)))
        claim #(eqv (sum 'F (s/succ %)) (add (at 'F s/nz) (sum tail %)))]
    (s/spec 'signed/expr-sum-value-head-tail [['F family] ['n nat]] (claim 'n)
            (s/induct claim (call 'signed/add-commutative zero (at 'F s/nz))
                      (fn [q ih]
                        (let [a (sum 'F (s/succ q)) b (at 'F s/nz) c (sum tail q) d (at 'F (s/succ q))]
                          (trans (add a d) (add (add b c) d) (add b (add c d))
                                 (s/add-cong a (add b c) d d ih (refl d))
                                 (call 'signed/add-associative b c d)))) 'n))))

(def bit-split-spec
  (let [b (sub one 'x) P (eqv 'x zero) Q (eqv b zero) R (eqv 'x one)
        final (disj P R)]
    (s/spec 'signed/zero-one-of-boolean-polynomial
            [['x signed] ['boolean (eqv (mul 'x b) zero)]] final
            (cases P Q final (call 'signed/multiply-zero-split 'x b 'boolean)
                   (f/lam [['h P]] (call 'proposition/left-disjunct P R 'h))
                   (f/lam [['h Q]]
                          (call 'proposition/right-disjunct P R
                                (sym one 'x
                                     (trans one (add b 'x) 'x
                                            (ring-eq one (add b 'x))
                                            (trans (add b 'x) (add zero 'x) 'x
                                                   (s/add-cong b zero 'x 'x 'h (refl 'x))
                                                   (ring-eq (add zero 'x) 'x))))))))))

(defn chain [a & steps]
  (if (empty? steps) (refl a)
      (let [[b h] (first steps)]
        (trans a b (first (last steps)) h (apply chain b (rest steps))))))

(defn sum-cong [F G n idx proof]
  (let [bound (symbol (str (name idx) "-bound"))]
    (s/sum-cong F G n (f/lam [[idx nat] [bound (nlt idx n)]] (proof idx bound)))))

(defn sum-mono [F G n idx proof]
  (let [bound (symbol (str (name idx) "-bound"))]
    (call 'signed/expr-sum-value-monotone-below F G n
          (f/lam [[idx nat] [bound (nlt idx n)]] (proof idx bound)))))

(def sum-sub-spec
  (let [NG (f/lam [['i nat]] (neg (at 'G 'i)))
        D (f/lam [['i nat]] (sub (at 'F 'i) (at 'G 'i)))
        SF (sum 'F 'n) SG (sum 'G 'n) SN (sum NG 'n)
        neg-proof (chain SN
                         [(s/map-sum NG 'n) (s/bridge NG 'n)]
                         [(neg (s/map-sum 'G 'n)) (s/list-law 'signed/map-sum-negate 'G (s/indices 'n))]
                         [(neg SG) (neg-cong (s/map-sum 'G 'n) SG
                                           (sym SG (s/map-sum 'G 'n) (s/bridge 'G 'n)))])]
    (s/spec 'signed/expr-sum-value-subtract [['F family] ['G family] ['n nat]]
            (eqv (sum D 'n) (sub SF SG))
            (chain (sum D 'n)
                   [(add SF SN) (call 'signed/expr-sum-value-add 'F NG 'n)]
                   [(sub SF SG) (s/add-cong SF SF SN (neg SG) (refl SF) neg-proof)]))))

(defn matrix-row [F i] (f/lam [['column-index nat]] (at F i 'column-index)))

(defn matrix-col [F j] (f/lam [['row-index nat]] (at F 'row-index j)))

(defn outflow [F n i] (sum (matrix-row F i) n))

(defn inflow [F n i] (sum (matrix-col F i) n))

(defn divergence [F n i] (sub (outflow F n i) (inflow F n i)))

(defn double-sum [F n] (sum (f/lam [['i nat]] (sum (matrix-row F 'i) n)) n))

(def matrix (f/arrow nat family))

(def divergence-spec
  (let [F 'F S 'S n 'n
        weighted (f/lam [['i nat]] (mul (at S 'i) (divergence F n 'i)))
        A (f/lam [['i nat]] (mul (at S 'i) (outflow F n 'i)))
        B (f/lam [['i nat]] (mul (at S 'i) (inflow F n 'i)))
        D (f/lam [['i nat]] (sub (at A 'i) (at B 'i)))
        L (f/lam [['i nat] ['j nat]] (mul (at S 'i) (at F 'i 'j)))
        T (f/lam [['i nat] ['j nat]] (mul (at S 'i) (at F 'j 'i)))
        R (f/lam [['i nat] ['j nat]] (mul (at S 'j) (at F 'i 'j)))
        LR (f/lam [['i nat]] (sum (matrix-row L 'i) n))
        RR (f/lam [['i nat]] (sum (matrix-row R 'i) n))
        TR (f/lam [['i nat]] (sum (matrix-row T 'i) n))
        rows-diff (f/lam [['i nat]] (sub (at LR 'i) (at RR 'i)))
        point-diff (f/lam [['i nat] ['j nat]] (sub (at L 'i 'j) (at R 'i 'j)))
        point-rows (f/lam [['i nat]] (sum (matrix-row point-diff 'i) n))
        delta (f/lam [['i nat] ['j nat]] (mul (sub (at S 'i) (at S 'j)) (at F 'i 'j)))
        delta-rows (f/lam [['i nat]] (sum (matrix-row delta 'i) n))
        out-eq (sum-cong A LR n 'u
                         (fn [u _] (call 'signed/expr-sum-value-scale-left (matrix-row F u) (at S u) n)))
        in-eq (chain (sum B n)
                     [(sum TR n) (sum-cong B TR n 'u
                                          (fn [u _] (call 'signed/expr-sum-value-scale-left (matrix-col F u) (at S u) n)))]
                     [(sum RR n) (call 'signed/expr-sum-value-swap T n n)])]
    (s/spec 'signed/expr-sum-weighted-divergence [['F matrix] ['S family] ['n nat]]
            (eqv (sum weighted n) (double-sum delta n))
            (chain (sum weighted n)
                   [(sum D n) (sum-cong weighted D n 'u (fn [u _] (ring-eq (mul (at S u) (divergence F n u))
                                                                                     (sub (mul (at S u) (outflow F n u)) (mul (at S u) (inflow F n u))))))]
                   [(sub (sum A n) (sum B n)) (call 'signed/expr-sum-value-subtract A B n)]
                   [(sub (sum LR n) (sum RR n))
                    (s/add-cong (sum A n) (sum LR n) (neg (sum B n)) (neg (sum RR n)) out-eq
                                (neg-cong (sum B n) (sum RR n) in-eq))]
                   [(sum rows-diff n) (sym (sum rows-diff n) (sub (sum LR n) (sum RR n))
                                           (call 'signed/expr-sum-value-subtract LR RR n))]
                   [(sum point-rows n)
                    (sum-cong rows-diff point-rows n 'u
                              (fn [u _] (sym (at point-rows u) (at rows-diff u)
                                             (call 'signed/expr-sum-value-subtract (matrix-row L u) (matrix-row R u) n))))]
                   [(sum delta-rows n)
                    (sum-cong point-rows delta-rows n 'u
                              (fn [u _] (sum-cong (matrix-row point-diff u) (matrix-row delta u) n 'v
                                                 (fn [v _] (ring-eq (sub (mul (at S u) (at F u v)) (mul (at S v) (at F u v)))
                                                                       (mul (sub (at S u) (at S v)) (at F u v)))))))]))))

(def boundary-spec
  (let [m 'm n (s/succ (s/succ m)) sink (s/succ m)
        W (f/lam [['i nat]] (mul (at 'S 'i) (at 'D 'i)))
        shift (f/lam [['q nat]] (at W (s/succ 'q))) Z (f/lam [['q nat]] zero)
        middle (sum shift m) first-term (at W s/nz) last-term (at W sink)
        middle-zero (chain middle
                           [(sum Z m) (sum-cong shift Z m 'q
                                                (fn [q hq]
                                                  (let [a (at 'S (s/succ q)) b (at 'D (s/succ q))]
                                                    (chain (mul a b)
                                                           [(mul a zero) (mul-cong a a b zero (refl a) (at 'internal q hq))]
                                                           [zero (ring-eq (mul a zero) zero)]))))]
                           [zero (call 'signed/expr-sum-value-zero m)])
        first-eq (chain first-term
                        [(mul one (at 'D s/nz)) (mul-cong (at 'S s/nz) one (at 'D s/nz) (at 'D s/nz) 'source (refl (at 'D s/nz)))]
                        [(at 'D s/nz) (ring-eq (mul one (at 'D s/nz)) (at 'D s/nz))])
        last-eq (chain last-term
                       [(mul zero (at 'D sink)) (mul-cong (at 'S sink) zero (at 'D sink) (at 'D sink) 'sink (refl (at 'D sink)))]
                       [zero (ring-eq (mul zero (at 'D sink)) zero)])
        rest-eq (chain (add middle last-term)
                       [(add zero zero) (s/add-cong middle zero last-term zero middle-zero last-eq)]
                       [zero (ring-eq (add zero zero) zero)])]
    (s/spec 'signed/expr-sum-conservation-boundary
            [['S family] ['D family] ['m nat]
             ['source (eqv (at 'S s/nz) one)] ['sink (eqv (at 'S sink) zero)]
             ['internal (s/all-below m #(eqv (at 'D (s/succ %)) zero))]]
            (eqv (sum W n) (at 'D s/nz))
            (chain (sum W n)
                   [(add first-term (add middle last-term)) (call 'signed/expr-sum-value-head-tail W sink)]
                   [(add (at 'D s/nz) zero)
                    (s/add-cong first-term (at 'D s/nz) (add middle last-term) zero first-eq rest-eq)]
                   [(at 'D s/nz) (ring-eq (add (at 'D s/nz) zero) (at 'D s/nz))]))))

(def edge-bound-spec
  (let [L (mul (sub 'a 'b) 'flow) R (mul (mul 'a (sub one 'b)) 'capacity)
        A0 (eqv 'a zero) A1 (eqv 'a one) B0 (eqv 'b zero) B1 (eqv 'b one)
        goal (le L R)
        case-proof
        (fn [av bv ha hb]
          (let [LL (mul (sub av bv) 'flow) RR (mul (mul av (sub one bv)) 'capacity)
                left (cond (= av bv) zero (= av one) 'flow :else (neg 'flow))
                right (if (and (= av one) (= bv zero)) 'capacity zero)
                l-eq (chain L
                            [LL (mul-cong (sub 'a 'b) (sub av bv) 'flow 'flow
                                          (s/add-cong 'a av (neg 'b) (neg bv) ha (neg-cong 'b bv hb)) (refl 'flow))]
                            [left (ring-eq LL left)])
                r-eq (chain R
                            [RR (mul-cong (mul 'a (sub one 'b)) (mul av (sub one bv)) 'capacity 'capacity
                                          (mul-cong 'a av (sub one 'b) (sub one bv) ha
                                                    (s/add-cong one one (neg 'b) (neg bv) (refl one) (neg-cong 'b bv hb)))
                                          (refl 'capacity))]
                            [right (ring-eq RR right)])
                ordered (cond (= av bv) (call 'signed/at-most-reflexive zero)
                              (= av one) 'capacity-bound
                              :else (call 'signed/negate-reverses-order zero 'flow 'nonnegative))]
            (s/le-transport left L right R (sym L left l-eq) (sym R right r-eq) ordered)))
        on-a (fn [av ha]
               (cases B0 B1 goal (call 'signed/zero-one-of-boolean-polynomial 'b 'b-bit)
                      (f/lam [['hb B0]] (case-proof av zero ha 'hb))
                      (f/lam [['hb B1]] (case-proof av one ha 'hb))))]
    (s/spec 'signed/flow-cut-edge-bound
            [['a signed] ['b signed] ['flow signed] ['capacity signed]
             ['a-bit (eqv (mul 'a (sub one 'a)) zero)]
             ['b-bit (eqv (mul 'b (sub one 'b)) zero)]
             ['nonnegative (le zero 'flow)] ['capacity-bound (le 'flow 'capacity)]]
            goal
            (cases A0 A1 goal (call 'signed/zero-one-of-boolean-polynomial 'a 'a-bit)
                   (f/lam [['ha A0]] (on-a zero 'ha))
                   (f/lam [['ha A1]] (on-a one 'ha))))))

(defn nodes [m] (s/succ (s/succ m)))

(defn all-pairs [n P]
  (f/forall [['u nat] ['hu (nlt 'u n)] ['v nat] ['hv (nlt 'v n)]] (P 'u 'v)))

(defn flow-nonnegative [F m] (all-pairs (nodes m) #(le zero (at F %1 %2))))

(defn flow-capacity [F C m] (all-pairs (nodes m) #(le (at F %1 %2) (at C %1 %2))))

(defn conservation [F m] (s/all-below m #(eqv (divergence F (nodes m) (s/succ %)) zero)))

(defn bits [S n] (s/all-below n #(eqv (mul (at S %) (sub one (at S %))) zero)))

(defn cut-matrix [C S]
  (f/lam [['i nat] ['j nat]] (mul (mul (at S 'i) (sub one (at S 'j))) (at C 'i 'j))))

(defn cut-capacity [C S n] (double-sum (cut-matrix C S) n))

(defn generic-hypotheses [F C S m]
  [['nonnegative (flow-nonnegative F m)] ['capacity (flow-capacity F C m)]
   ['conservation (conservation F m)] ['bits (bits S (nodes m))]
   ['source (eqv (at S s/nz) one)] ['sink (eqv (at S (s/succ m)) zero)]])

(def weak-duality-spec
  (let [n (nodes 'm) D (f/lam [['i nat]] (divergence 'F n 'i))
        W (f/lam [['i nat]] (mul (at 'S 'i) (at D 'i)))
        Delta (f/lam [['i nat] ['j nat]] (mul (sub (at 'S 'i) (at 'S 'j)) (at 'F 'i 'j)))
        K (cut-matrix 'C 'S)
        DR (f/lam [['i nat]] (sum (matrix-row Delta 'i) n))
        KR (f/lam [['i nat]] (sum (matrix-row K 'i) n))
        value (divergence 'F n s/nz)
        boundary (call 'signed/expr-sum-conservation-boundary 'S D 'm 'source 'sink 'conservation)
        to-delta (trans value (sum W n) (double-sum Delta n)
                        (sym (sum W n) value boundary)
                        (call 'signed/expr-sum-weighted-divergence 'F 'S n))
        ordered (sum-mono DR KR n 'u
                          (fn [u hu]
                            (sum-mono (matrix-row Delta u) (matrix-row K u) n 'v
                                      (fn [v hv]
                                        (call 'signed/flow-cut-edge-bound (at 'S u) (at 'S v) (at 'F u v) (at 'C u v)
                                              (at 'bits u hu) (at 'bits v hv)
                                              (at 'nonnegative u hu v hv) (at 'capacity u hu v hv))))))]
    (s/spec 'signed/expr-sum-flow-cut-weak-duality
            (into [['F matrix] ['C matrix] ['S family] ['m nat]] (generic-hypotheses 'F 'C 'S 'm))
            (le value (cut-capacity 'C 'S n))
            (le-trans value (double-sum Delta n) (cut-capacity 'C 'S n)
                      (eq-le value (double-sum Delta n) to-delta) ordered))))

(defn flat-cut [C S n]
  (sum (f/lam [['e nat]]
              (mul (mul (at S (call 'nat/row-of n 'e)) (sub one (at S (call 'nat/col-of n 'e))))
                   (at C 'e))) (nmul n n)))

(defn flat-matrix [C n]
  (f/lam [['i nat] ['j nat]] (at C (nadd 'j (nmul 'i n)))))

(def flat-cut-spec
  (let [C 'C S 'S n 'n
        term (fn [e i j] (mul (mul (at S i) (sub one (at S j))) (at C e)))
        H (f/lam [['e nat]] (term 'e (call 'nat/row-of n 'e) (call 'nat/col-of n 'e)))
        R (f/lam [['i nat]] (sum (f/lam [['j nat]] (at H (nadd 'j (nmul 'i n)))) n))
        K (cut-matrix (flat-matrix C n) S)
        KR (f/lam [['i nat]] (sum (matrix-row K 'i) n))
        point (fn [u v hv]
                (let [e (nadd v (nmul u n)) r (call 'nat/row-of n e) c (call 'nat/col-of n e)
                      a (term e r c) b (term e u c) d (term e u v)
                      hr (call 'nat/row-of-pair-index n v u hv)
                      hc (call 'nat/col-of-pair-index n v u hv)]
                  (trans a b d
                         (nsubst r u hr (f/lam [['replacement nat]] (eqv a (term e 'replacement c))) (refl a))
                         (nsubst c v hc (f/lam [['replacement nat]] (eqv b (term e u 'replacement))) (refl b)))))]
    (s/spec 'signed/expr-sum-flat-cut-as-matrix [['C family] ['S family] ['n nat]]
            (eqv (flat-cut C S n) (cut-capacity (flat-matrix C n) S n))
            (chain (flat-cut C S n)
                   [(sum R n) (call 'signed/expr-sum-value-rectangular H n n)]
                   [(sum KR n)
                    (sum-cong R KR n 'u
                              (fn [u _]
                                (sum-cong (f/lam [['j nat]] (at H (nadd 'j (nmul u n))))
                                          (matrix-row K u) n 'v (fn [v hv] (point u v hv)))))]))))

(defn conjunction [parts]
  (if (= 1 (count parts)) (first parts)
      (call 'proposition/conjunction (first parts) (conjunction (rest parts)))))

(defn extract [parts i h]
  (if (= 1 (count parts)) h
      (if (zero? i) (call 'proposition/left (first parts) (conjunction (rest parts)) h)
          (extract (rest parts) (dec i) (call 'proposition/right (first parts) (conjunction (rest parts)) h)))))

(def theorem-specs [flatten-spec head-tail-spec bit-split-spec sum-sub-spec divergence-spec boundary-spec edge-bound-spec weak-duality-spec flat-cut-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with :expr-sum-flowcut-duality theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.flow-cut))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
