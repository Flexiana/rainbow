(ns rainbow.math.lemmas.fcast-readings
  "General lemmas: fcast readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.claimpay-readings :as clp]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.lemmas.cpm-makespan :as cpm]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-order :as multiply-order]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.map-sum-algebra :as map-sum]
            [rainbow.math.linear.vector.norm-nonnegative :as norm-nn]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.rational.signed.add-associative :as add-associative]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.equivalence-laws :as equivalence]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.module :as module]))

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

(defn abs-facts [v W] (pconj (disj (eqv W v) (eqv W (neg v))) (pconj (le s/zero W) (pconj (le v W) (le (neg v) W)))))

(def abs-pair-spec
  (let [v 'ab-v A (pp v) B (pp (neg v)) W (add A B)
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        parts (fn [u pu]
                (let [f* (call 'signed/positive-part-cases u) rest-t (pconj (le u pu) (disj (eqv pu s/zero) (eqv pu u)))]
                  {:nn (fst (le s/zero pu) rest-t f*)
                   :lo (fst (le u pu) (disj (eqv pu s/zero) (eqv pu u)) (snd (le s/zero pu) rest-t f*))
                   :or (snd (le u pu) (disj (eqv pu s/zero) (eqv pu u)) (snd (le s/zero pu) rest-t f*))}))
        PA (parts v A) PB (parts (neg v) B)
        r1 (fn [x y] (ring-atoms [['ab-x v]] x y))
        nn (le-resp (add s/zero s/zero) s/zero W W (r1 (add s/zero s/zero) s/zero) (refl W) (call 'signed/add-monotone s/zero A s/zero B (:nn PA) (:nn PB)))
        lo (le-resp (add v s/zero) v W W (r1 (add v s/zero) v) (refl W) (call 'signed/add-monotone v A s/zero B (:lo PA) (:nn PB)))
        nlo (le-resp (add s/zero (neg v)) (neg v) W W (r1 (add s/zero (neg v)) (neg v)) (refl W) (call 'signed/add-monotone s/zero A (neg v) B (:nn PA) (:lo PB)))
        D (disj (eqv W v) (eqv W (neg v)))
        L (fn [h] (inl (eqv W v) (eqv W (neg v)) h)) R (fn [h] (inr (eqv W v) (eqv W (neg v)) h))
        ;; W ~ x + y from A ~ x and B ~ y
        wv (fn [x y ha hb] (acong A x B y ha hb))
        ;; v ~ 0 from v <= 0 and 0 <= v
        v0 (fn [hle hge] (anti v s/zero hle hge))
        ;; 0 <= v from -v <= 0
        ge-of-neg (fn [h] (le-resp (add (neg v) v) s/zero (add s/zero v) v (r1 (add (neg v) v) s/zero) (r1 (add s/zero v) v)
                                   (call 'signed/add-right-monotone (neg v) s/zero v h)))
        ;; v <= 0 from 0 <= -v
        le-of-neg (fn [h] (le-resp (add s/zero v) v (add (neg v) v) s/zero (r1 (add s/zero v) v) (r1 (add (neg v) v) s/zero)
                                   (call 'signed/add-right-monotone s/zero (neg v) v h)))
        tr (fn [x y z h k] (trans x y z h k))
        case-a0 (f/lam [['ab-a0 (eqv A s/zero)]]
                       (cases (eqv B s/zero) (eqv B (neg v)) D (:or PB)
                              (f/lam [['ab-b0 (eqv B s/zero)]]
                                     (let [v-le (le-resp v v A s/zero (refl v) 'ab-a0 (:lo PA))
                                           nv-le (le-resp (neg v) (neg v) B s/zero (refl (neg v)) 'ab-b0 (:lo PB))
                                           hv (v0 v-le (ge-of-neg nv-le))]
                                       (L (tr W (add s/zero s/zero) v (wv s/zero s/zero 'ab-a0 'ab-b0)
                                              (tr (add s/zero s/zero) s/zero v (r1 (add s/zero s/zero) s/zero) (sym v s/zero hv))))))
                              (f/lam [['ab-bn (eqv B (neg v))]]
                                     (R (tr W (add s/zero (neg v)) (neg v) (wv s/zero (neg v) 'ab-a0 'ab-bn) (r1 (add s/zero (neg v)) (neg v)))))))
        case-av (f/lam [['ab-av (eqv A v)]]
                       (cases (eqv B s/zero) (eqv B (neg v)) D (:or PB)
                              (f/lam [['ab-b0 (eqv B s/zero)]]
                                     (L (tr W (add v s/zero) v (wv v s/zero 'ab-av 'ab-b0) (r1 (add v s/zero) v))))
                              (f/lam [['ab-bn (eqv B (neg v))]]
                                     (let [v-ge (le-resp s/zero s/zero A v (refl s/zero) 'ab-av (:nn PA))
                                           nv-ge (le-resp s/zero s/zero B (neg v) (refl s/zero) 'ab-bn (:nn PB))
                                           hv (v0 (le-of-neg nv-ge) v-ge)]
                                       (L (tr W (add v (neg v)) v (wv v (neg v) 'ab-av 'ab-bn)
                                              (tr (add v (neg v)) s/zero v (r1 (add v (neg v)) s/zero) (sym v s/zero hv))))))))]
    (s/spec 'signed/abs-pair-cases [[v signed]]
            (abs-facts v W)
            (conjoin D (pconj (le s/zero W) (pconj (le v W) (le (neg v) W)))
                     (cases (eqv A s/zero) (eqv A v) D (:or PA) case-a0 case-av)
                     (conjoin (le s/zero W) (pconj (le v W) (le (neg v) W)) nn
                              (conjoin (le v W) (le (neg v) W) lo nlo))))))

(defn ofn [n] (of-nat/of-nat n))

(defn wfam [ef] (f/lam [['fw-t nat]] (add (pp (at ef 'fw-t)) (pp (neg (at ef 'fw-t))))))

(defn sqfam [ef] (f/lam [['fs-t nat]] (mul (at ef 'fs-t) (at ef 'fs-t))))

(defn devfam [ef M] (f/lam [['fd-t nat]] (mul (sub (at ef 'fd-t) M) (sub (at ef 'fd-t) M))))

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

(def square-spec
  (let [[e m] '[sd-e sd-m] d (sub e m) ee (mul e e) me (mul m e) mm (mul m m) em (mul e m)
        rhs (add ee (add mm (neg (mul (add m m) e))))
        L1 (add (mul e d) (mul (neg m) d))
        h-e (chain [(mul e d) (add ee (mul e (neg m))) (add ee (neg em)) (add ee (neg me))]
                   [(dl e e (neg m)) (acong ee ee (mul e (neg m)) (neg em) (refl ee) (mul-neg e m))
                    (acong ee ee (neg em) (neg me) (refl ee) (negc em me (call 'signed/multiply-commutative e m)))])
        h-m (chain [(mul (neg m) d) (add (mul (neg m) e) (mul (neg m) (neg m))) (add (neg me) mm)]
                   [(dl (neg m) e (neg m))
                    (acong (mul (neg m) e) (neg me) (mul (neg m) (neg m)) mm (neg-mul m e)
                           (ring-atoms [['sq-m m]] (mul (neg 'sq-m) (neg 'sq-m)) (mul 'sq-m 'sq-m)))])
        h-r (acong ee ee (add mm (neg (mul (add m m) e))) (add mm (neg (add me me))) (refl ee)
                   (acong mm mm (neg (mul (add m m) e)) (neg (add me me)) (refl mm) (negc (mul (add m m) e) (add me me) (dr m m e))))
        R2 (add ee (add mm (neg (add me me))))]
    (s/spec 'signed/square-difference-expand [[e signed] [m signed]]
            (eqv (mul d d) rhs)
            (chain [(mul d d) L1 (add (add ee (neg me)) (add (neg me) mm)) R2 rhs]
                   [(dr e (neg m) d)
                    (acong (mul e d) (add ee (neg me)) (mul (neg m) d) (add (neg me) mm) h-e h-m)
                    (ring-atoms [['sx-a ee] ['sx-b me] ['sx-c mm]]
                                (add (add 'sx-a (neg 'sx-b)) (add (neg 'sx-b) 'sx-c)) (add 'sx-a (add 'sx-c (neg (add 'sx-b 'sx-b)))))
                    (sym rhs R2 h-r)]))))

(defn generic-parts [ef q ME MAE MSE hME hMAE hMSE]
  (let [n (s/succ q) N (ofn n) Wf (wfam ef) Sq (sqfam ef)
        hpos (call 'signed/of-nat-successor-positive q)
        cancel (fn [x y h] (call 'signed/at-most-cancel-positive-right x y N hpos
                                 (le-resp (mul N x) (mul x N) (mul N y) (mul y N)
                                          (call 'signed/multiply-commutative N x) (call 'signed/multiply-commutative N y) h)))
        fst (fn [P Q h] (call 'proposition/left P Q h)) snd (fn [P Q h] (call 'proposition/right P Q h))
        ab (fn [t] (call 'signed/abs-pair-cases (at ef t)))
        part (fn [t k] (let [v (at ef t) W (at Wf t) D (disj (eqv W v) (eqv W (neg v)))
                             R1 (pconj (le s/zero W) (pconj (le v W) (le (neg v) W))) R2 (pconj (le v W) (le (neg v) W))
                             r1 (snd D R1 (ab t))]
                         (case k :nn (fst (le s/zero W) R2 r1) :lo (fst (le v W) (le (neg v) W) (snd (le s/zero W) R2 r1))
                                 :nlo (snd (le v W) (le (neg v) W) (snd (le s/zero W) R2 r1)))))
        ;; |bias| <= MAE
        sMAE-nn (call 'signed/expr-sum-value-nonnegative Wf n (f/lam [['fn-t nat] ['fn-h (below 'fn-t n)]] (part 'fn-t :nn)))
        mae-nn (cancel s/zero MAE (le-resp s/zero (mul N s/zero) (sum Wf n) (mul N MAE)
                                           (sym (mul N s/zero) s/zero (call 'signed/multiply-zero-right N)) (sym (mul N MAE) (sum Wf n) hMAE) sMAE-nn))
        me-le (cancel ME MAE (le-resp (sum ef n) (mul N ME) (sum Wf n) (mul N MAE) (sym (mul N ME) (sum ef n) hME) (sym (mul N MAE) (sum Wf n) hMAE)
                                      (call 'signed/expr-sum-value-monotone-below ef Wf n (f/lam [['fl-t nat] ['fl-h (below 'fl-t n)]] (part 'fl-t :lo)))))
        NE (f/lam [['ng nat]] (neg (at ef 'ng)))
        sNE (chain [(sum NE n) (neg (sum ef n)) (neg (mul N ME)) (mul N (neg ME))]
                   [(call 'signed/expr-sum-value-negate ef n) (negc (sum ef n) (mul N ME) (sym (mul N ME) (sum ef n) hME))
                    (ring-atoms [['fz-n N] ['fz-m ME]] (neg (mul 'fz-n 'fz-m)) (mul 'fz-n (neg 'fz-m)))])
        nme-le (cancel (neg ME) MAE (le-resp (sum NE n) (mul N (neg ME)) (sum Wf n) (mul N MAE) sNE (sym (mul N MAE) (sum Wf n) hMAE)
                                             (call 'signed/expr-sum-value-monotone-below NE Wf n (f/lam [['fm-t nat] ['fm-h (below 'fm-t n)]] (part 'fm-t :nlo)))))
        p2 (conjoin (le s/zero MAE) (pconj (le ME MAE) (le (neg ME) MAE)) mae-nn (conjoin (le ME MAE) (le (neg ME) MAE) me-le nme-le))
        ;; the bias-variance split
        M ME C (mul M M) K (add M M) Tf (devfam ef M)
        Yf (f/lam [['fy-t nat]] (add C (neg (mul K (at ef 'fy-t)))))
        XY (f/lam [['fx-t nat]] (add (at Sq 'fx-t) (at Yf 'fx-t)))
        Cf (f/lam [['ci nat]] C) KE (f/lam [['fk-t nat]] (mul K (at ef 'fk-t))) NKE (f/lam [['ng nat]] (neg (at KE 'ng)))
        CN (mul C N) sT (sum Tf n)
        term (f/lam [['ft-t nat] ['ft-h (below 'ft-t n)]] (call 'signed/square-difference-expand (at ef 'ft-t) M))
        sY (chain [(sum Yf n) (add (sum Cf n) (sum NKE n)) (add CN (neg (sum KE n))) (add CN (neg (mul K (sum ef n))))]
                  [(call 'signed/expr-sum-value-add Cf NKE n)
                   (acong (sum Cf n) CN (sum NKE n) (neg (sum KE n)) (call 'signed/expr-sum-constant-of-nat C n) (call 'signed/expr-sum-value-negate KE n))
                   (acong CN CN (neg (sum KE n)) (neg (mul K (sum ef n))) (refl CN)
                          (negc (sum KE n) (mul K (sum ef n)) (sym (mul K (sum ef n)) (sum KE n) (call 'signed/expr-sum-value-scale-left ef K n))))])
        MNM (mul M (mul N M))
        hk (chain [(mul K (mul N M)) (add MNM MNM) (add CN CN)]
                  [(dr M M (mul N M))
                   (let [h1 (chain [MNM (mul M (mul M N)) CN]
                                   [(mcong M M (mul N M) (mul M N) (refl M) (call 'signed/multiply-commutative N M))
                                    (sym CN (mul M (mul M N)) (call 'signed/multiply-associative M M N))])]
                     (acong MNM CN MNM CN h1 h1))])
        A (mul N MSE)
        hS (chain [sT (sum XY n) (add (sum Sq n) (sum Yf n)) (add A (add CN (neg (mul K (sum ef n)))))
                   (add A (add CN (neg (mul K (mul N M))))) (add A (add CN (neg (add CN CN)))) (add A (neg CN))]
                  [(call 'signed/expr-sum-value-respects-equivalence-below Tf XY n term)
                   (call 'signed/expr-sum-value-add Sq Yf n)
                   (acong (sum Sq n) A (sum Yf n) (add CN (neg (mul K (sum ef n)))) (sym A (sum Sq n) hMSE) sY)
                   (acong A A (add CN (neg (mul K (sum ef n)))) (add CN (neg (mul K (mul N M)))) (refl A)
                          (acong CN CN (neg (mul K (sum ef n))) (neg (mul K (mul N M))) (refl CN)
                                 (negc (mul K (sum ef n)) (mul K (mul N M)) (mcong K K (sum ef n) (mul N M) (refl K) (sym (mul N M) (sum ef n) hME)))))
                   (acong A A (add CN (neg (mul K (mul N M)))) (add CN (neg (add CN CN))) (refl A)
                          (acong CN CN (neg (mul K (mul N M))) (neg (add CN CN)) (refl CN) (negc (mul K (mul N M)) (add CN CN) hk)))
                   (ring-atoms [['fv-a A] ['fv-c CN]] (add 'fv-a (add 'fv-c (neg (add 'fv-c 'fv-c)))) (add 'fv-a (neg 'fv-c)))])
        split (chain [A (add CN (add A (neg CN))) (add CN sT)]
                     [(ring-atoms [['fp-a A] ['fp-c CN]] 'fp-a (add 'fp-c (add 'fp-a (neg 'fp-c))))
                      (acong CN CN (add A (neg CN)) sT (refl CN) (sym sT (add A (neg CN)) hS))])
        sT-nn (call 'signed/expr-sum-value-nonnegative Tf n
                    (f/lam [['fq-t nat] ['fq-h (below 'fq-t n)]]
                           (let [d (sub (at ef 'fq-t) M)] (call 'signed/zero-at-most-of-nonnegative (mul d d) (call 'signed/square-nonnegative d)))))
        cn-le (le-resp (add s/zero CN) (mul N C) (add sT CN) A
                       (trans (add s/zero CN) CN (mul N C) (ring-atoms [['fo-c CN]] (add s/zero 'fo-c) 'fo-c) (call 'signed/multiply-commutative C N))
                       (trans (add sT CN) (add CN sT) A (call 'signed/add-commutative sT CN) (sym A (add CN sT) split))
                       (call 'signed/add-right-monotone s/zero sT CN sT-nn))
        p3 (conjoin (eqv A (add CN sT)) (le C MSE) split (cancel C MSE cn-le))]
    {:p2 p2 :p3 p3}))

(defn P2-of [ME MAE] (pconj (le s/zero MAE) (pconj (le ME MAE) (le (neg ME) MAE))))

(defn P3-of [ef q ME MSE] (let [n (s/succ q) N (ofn n)]
                            (pconj (eqv (mul N MSE) (add (mul (mul ME ME) N) (sum (devfam ef ME) n))) (le (mul ME ME) MSE))))

(def bias-spec
  (let [[F j ME MAE] '[fb-f fb-j fb-me fb-mae] n (s/succ j) N (ofn n)
        hyps [['fb-hme (eqv (mul N ME) (sum F n))] ['fb-hmae (eqv (mul N MAE) (sum (wfam F) n))]]]
    (s/spec 'signed/forecast-bias-bound (into [[F family] [j nat] [ME signed] [MAE signed]] hyps)
            (P2-of ME MAE)
            (:p2 (generic-parts F j ME MAE s/zero 'fb-hme 'fb-hmae nil)))))

(def variance-spec
  (let [[F j ME MSE] '[fv-f fv-j fv-me fv-mse] n (s/succ j) N (ofn n)
        hyps [['fv-hme (eqv (mul N ME) (sum F n))] ['fv-hmse (eqv (mul N MSE) (sum (sqfam F) n))]]]
    (s/spec 'signed/forecast-variance-split (into [[F family] [j nat] [ME signed] [MSE signed]] hyps)
            (P3-of F j ME MSE)
            (:p3 (generic-parts F j ME s/zero MSE 'fv-hme nil 'fv-hmse)))))

(def borrowed-specs [clp/pp-spec mmck/cancel-positive-spec mmck/successor-positive-spec pcmax/cancel-order-spec cpm/sum-negate-spec])

(def theorem-specs [abs-pair-spec square-spec bias-spec variance-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring rainbow.math.rational.signed.distributive rainbow.math.linear.matrix.row-length-shape rainbow.math.linear.matrix.row-length-decider rainbow.math.rational.signed.structural-equality rainbow.math.linear.vector.equivalence rainbow.math.linear.vector.uniform-clamp rainbow.math.linear.vector.pointwise-order rainbow.math.linear.matrix.action-prepend rainbow.math.linear.matrix.action-associative rainbow.math.linear.matrix.transpose-multiply rainbow.math.linear.matrix.transpose-shape rainbow.math.linear.matrix.transpose-involution rainbow.math.linear.matrix.transpose-involution-positive rainbow.math.linear.matrix.transpose-multiply-reverse rainbow.math.linear.matrix.composable-transpose rainbow.math.linear.matrix.associativity-counterexample rainbow.math.linear.matrix.signed-scale rainbow.math.linear.matrix.signed-scale-right rainbow.math.linear.matrix.add rainbow.math.linear.matrix.add-shape rainbow.math.linear.matrix.prepend-add rainbow.math.linear.matrix.add-right rainbow.math.linear.matrix.add-algebra rainbow.math.linear.matrix.additive-group rainbow.math.linear.matrix.negate-linear rainbow.math.linear.matrix.subtract-linear rainbow.math.linear.matrix.signed-scale-algebra rainbow.math.linear.matrix.signed-scale-units rainbow.math.linear.matrix.signed-scale-congruence rainbow.math.linear.matrix.signed-scale-subtract rainbow.math.rational.signed.distance-multiply-nonnegative rainbow.math.rational.signed.vector-sup-distance rainbow.algorithms.proofs.inner-product rainbow.math.rational.signed.distance-triangle rainbow.math.rational.signed.distance-translation rainbow.math.rational.signed.distance-additive rainbow.math.linear.vector.dot-distance-bound rainbow.math.linear.vector.row-sum-lipschitz rainbow.math.linear.matrix.action-sup-bound rainbow.math.linear.matrix.signed-scale-order rainbow.math.linear.matrix.pointwise-order-laws rainbow.math.linear.matrix.signed-scale-antitone rainbow.math.linear.matrix.add-order rainbow.math.linear.matrix.signed-scale-positive rainbow.math.linear.matrix.signed-scale-sign rainbow.math.linear.matrix.positive-action rainbow.math.linear.matrix.transpose-order rainbow.math.linear.matrix.positive-multiply rainbow.math.linear.matrix.gram-positive rainbow.math.linear.matrix.gram-kernel rainbow.math.linear.matrix.row-gram rainbow.math.linear.matrix.row-gram-kernel rainbow.math.linear.vector.norm-pythagorean rainbow.math.linear.matrix.least-squares-normal rainbow.math.linear.matrix.least-squares-equality rainbow.math.linear.matrix.mixed-sign-action rainbow.math.linear.matrix.mixed-sign-multiply rainbow.math.linear.matrix.antitone rainbow.math.linear.matrix.interval-order rainbow.math.linear.matrix.affine-order rainbow.math.linear.matrix.linear rainbow.math.rational.signed.vector-sup-congruence rainbow.math.finite.vector rainbow.math.linear.vector.pointwise-order-laws rainbow.math.linear.vector.add-order rainbow.math.rational.signed.vector-sup-translation rainbow.math.linear.matrix.affine-sup-distance rainbow.math.linear.matrix.row-sum-lipschitz rainbow.math.linear.matrix.row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.half-row-sum-fixed-point-uniqueness rainbow.math.linear.matrix.affine-half-iterate-contraction rainbow.math.linear.matrix.affine-half-iterate-rate rainbow.math.rational.signed.geometric-bridge rainbow.math.linear.matrix.affine-half-iterate-converges rainbow.math.linear.matrix.affine-strong-row-contraction rainbow.math.linear.matrix.affine-residual-certificate rainbow.math.linear.matrix.affine-inverse-gap-certificate rainbow.math.linear.matrix.affine-general-rate-certificate rainbow.math.sums.of-nat rainbow.math.lemmas.one-center rainbow.math.rational.signed.multiply-associative])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-fcast-readings borrowed-specs) (support/extend-with-shared :expr-sum-fcast-readings theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.fcast-readings))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
