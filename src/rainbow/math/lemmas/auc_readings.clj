(ns rainbow.math.lemmas.auc-readings
  "General lemmas: auc readings. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.pcmax-lower-bound :as pcmax]
            [rainbow.math.lemmas.prf-readings :as prf]
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

(def two (of-nat/of-nat (s/succ (s/succ s/nz))))

(def btrue (f/const* 'data/true []))

(def bfalse (f/const* 'data/false []))

(defn selb [at-false at-true c] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true c))

(defn cle "a closed a <= b by computation" [x y]
  (call 'signed/decide-at-most-true-sound x y (f/app (f/const* 'equality/reflexive [type-level]) bool btrue)))

(defn weight [b1 b2] (add (mul two (selb one s/zero b1)) (selb s/zero (selb s/zero one b2) b1)))

(defn wclaim [b1 b2] (let [w (weight b1 b2)] (pconj (le s/zero w) (le w two))))

(defn closed-case [b1 b2] (let [w (weight b1 b2)] (conjoin (le s/zero w) (le w two) (cle s/zero w) (cle w two))))

(def weight-spec
  (s/spec 'signed/auc-weight-bounds [['aw-b1 bool] ['aw-b2 bool]]
          (wclaim 'aw-b1 'aw-b2)
          (f/app (f/app (f/const* 'data/Bool.rec [prop-level])
                        (f/lam [['aw-c1 bool]] (f/forall [['aw-c2 bool]] (wclaim 'aw-c1 'aw-c2)))
                        (f/lam [['aw-f2 bool]] (closed-case bfalse 'aw-f2))
                        (f/lam [['aw-t2 bool]]
                               (f/app (f/const* 'data/Bool.rec [prop-level])
                                      (f/lam [['aw-c3 bool]] (wclaim btrue 'aw-c3))
                                      (closed-case btrue bfalse) (closed-case btrue btrue) 'aw-t2))
                        'aw-b1)
                 'aw-b2)))

(def complement-spec
  (let [y 'cn-y]
    (s/spec 'signed/complement-nonnegative [[y signed] ['cn-h (eqv (mul y (sub one y)) s/zero)]]
            (le s/zero (sub one y))
            (call 'signed/zero-one-nonnegative (sub one y)
                  (chain [(mul (sub one y) (sub one (sub one y))) (mul (sub one y) y) (mul y (sub one y)) s/zero]
                         [(mcong (sub one y) (sub one y) (sub one (sub one y)) y (refl (sub one y))
                                 (ring-atoms [['cn-o one] ['cn-v y]] (sub 'cn-o (sub 'cn-o 'cn-v)) 'cn-v))
                          (call 'signed/multiply-commutative (sub one y) y)
                          'cn-h])))))

(def unit-spec
  (let [[A P N W] '[au-a au-p au-n au-w] PN (mul P N)
        two-pos (call 'signed/of-nat-successor-positive (s/succ s/nz))
        pp (call 'signed/positive-of-at-least-one P 'au-hp) pn (call 'signed/positive-of-at-least-one N 'au-hn)
        ;; c * two  <=  d * two  from  two (c ...) forms
        uncanc2 (fn [x y h] (call 'signed/at-most-cancel-positive-right x y two two-pos
                                  (le-resp (mul two x) (mul x two) (mul two y) (mul y two)
                                           (call 'signed/multiply-commutative two x) (call 'signed/multiply-commutative two y) h)))
        ;; x (P N) <= y (P N)  ->  x <= y
        uncancPN (fn [x y h] (let [re (fn [z] (chain [(mul z PN) (mul z (mul N P)) (mul (mul z N) P)]
                                                     [(mcong z z PN (mul N P) (refl z) (call 'signed/multiply-commutative P N))
                                                      (sym (mul (mul z N) P) (mul z (mul N P)) (call 'signed/multiply-associative z N P))]))
                                   h1 (call 'signed/at-most-cancel-positive-right (mul x N) (mul y N) P pp
                                            (le-resp (mul x PN) (mul (mul x N) P) (mul y PN) (mul (mul y N) P) (re x) (re y) h))]
                               (call 'signed/at-most-cancel-positive-right x y N pn h1)))
        lhs (mul two (mul A PN))
        up (le-resp W lhs (mul two PN) (mul two PN) (sym lhs W 'au-h) (refl (mul two PN)) 'au-h1)
        up2 (uncanc2 (mul A PN) PN up)
        a1 (uncancPN A one (le-resp (mul A PN) (mul A PN) PN (mul one PN) (refl (mul A PN)) (sym (mul one PN) PN (call 'signed/multiply-one-left PN)) up2))
        lo (le-resp s/zero (mul two s/zero) W lhs (sym (mul two s/zero) s/zero (call 'signed/multiply-zero-right two)) (sym lhs W 'au-h) 'au-h0)
        lo2 (uncanc2 s/zero (mul A PN) lo)
        zPN (sym (mul s/zero PN) s/zero (ring-atoms [['az-x PN]] (mul s/zero 'az-x) s/zero))
        a0 (uncancPN s/zero A (le-resp s/zero (mul s/zero PN) (mul A PN) (mul A PN) zPN (refl (mul A PN)) lo2))]
    (s/spec 'signed/auc-unit-interval
            [[A signed] [P signed] [N signed] [W signed]
             ['au-h (eqv lhs W)] ['au-h0 (le s/zero W)] ['au-h1 (le W (mul two PN))] ['au-hp (le one P)] ['au-hn (le one N)]]
            (pconj (le s/zero A) (le A one))
            (conjoin (le s/zero A) (le A one) a0 a1))))

(defn dec [x y] (call 'signed/decide-at-most x y))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec mmck/cancel-positive-spec mmck/successor-positive-spec pcmax/cancel-order-spec prf/positive-spec])

(def theorem-specs [weight-spec complement-spec unit-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
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
      (support/extend-with-shared :expr-sum-auc-readings theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
