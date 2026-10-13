(ns rainbow.math.lemmas.weighted-cover-rounding
  "General lemmas: weighted cover rounding. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.mmck-unique :as mmck]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-associative :as multiply-associative]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn sub [x y] (a/sub x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn rmono [c x y hc h] (call 'signed/multiply-right-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn times-one [x] (a/chain (mul x one) [(mul one x) (call 'signed/multiply-commutative x one)] [x (one-times x)]))

(defn comm [x y] (call 'signed/multiply-commutative x y))

(defn assoc* [x y z] (call 'signed/multiply-associative x y z))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (lmono p s/zero q hp hq)))

(defn zero-one [x] (eqv (mul x (sub one x)) s/zero))

(defn edge-load [B z n e] (sum (f/lam [['lv nat]] (mul (at B e 'lv) (at z 'lv))) n))

(defn vertex-price [B y E v] (sum (f/lam [['pe nat]] (mul (at B 'pe v) (at y 'pe))) E))

(defn weighted [w z n] (sum (f/lam [['wv nat]] (mul (at w 'wv) (at z 'wv))) n))

(defn competitor-binders [B z n E]
  [['hz (s/all-below n #(le s/zero (at z %)))]
   ['hcov (s/all-below E #(le one (edge-load B z n %)))]])

(def weak-duality-spec
  (let [B 'B w 'w y 'y z 'z n 'n E 'E
        Y (sum (f/lam [['ye nat]] (at y 'ye)) E)
        T (fn [e v] (mul (at y e) (mul (at B e v) (at z v))))
        S1 (f/lam [['s1 nat]] (mul (at y 's1) (edge-load B z n 's1)))
        S2 (f/lam [['s2 nat]] (sum (f/lam [['s2v nat]] (T 's2 's2v)) n))
        S3 (f/lam [['s3 nat]] (sum (f/lam [['s3e nat]] (T 's3e 's3)) E))
        S4 (f/lam [['s4 nat]] (mul (vertex-price B y E 's4) (at z 's4)))
        WZ (f/lam [['s5 nat]] (mul (at w 's5) (at z 's5)))
        step1 (a/sum-mono (f/lam [['ye nat]] (at y 'ye)) S1 E 'wa
                          (fn [e he] (le-resp (mul (at y e) one) (at y e) (mul (at y e) (edge-load B z n e)) (mul (at y e) (edge-load B z n e))
                                              (times-one (at y e)) (refl (mul (at y e) (edge-load B z n e)))
                                              (lmono (at y e) one (edge-load B z n e) (at 'hy e he) (at 'hcov e he)))))
        eq2 (a/sum-cong S1 S2 E 'wb
                        (fn [e _] (call 'signed/expr-sum-value-scale-left (f/lam [['sv nat]] (mul (at B e 'sv) (at z 'sv))) (at y e) n)))
        eq3 (call 'signed/expr-sum-value-swap (f/lam [['te nat] ['tv nat]] (T 'te 'tv)) n E)
        eq4 (a/sum-cong S3 S4 n 'wc
                        (fn [v _]
                          (let [G (f/lam [['ge nat]] (mul (mul (at B 'ge v) (at y 'ge)) (at z v)))]
                            (a/chain (sum (f/lam [['s3e nat]] (T 's3e v)) E)
                                     [(sum G E)
                                      (a/sum-cong (f/lam [['s3e nat]] (T 's3e v)) G E 'wd
                                                  (fn [e _] (let [ye (at y e) b (at B e v) zv (at z v)]
                                                              (a/chain (mul ye (mul b zv))
                                                                       [(mul (mul ye b) zv) (sym (mul (mul ye b) zv) (mul ye (mul b zv)) (assoc* ye b zv))]
                                                                       [(mul (mul b ye) zv) (mcong (mul ye b) (mul b ye) zv zv (comm ye b) (refl zv))]))))]
                                     [(mul (vertex-price B y E v) (at z v))
                                      (sym (mul (vertex-price B y E v) (at z v)) (sum G E)
                                           (call 'signed/expr-sum-value-scale-right (f/lam [['pe nat]] (mul (at B 'pe v) (at y 'pe))) (at z v) E))]))))
        step5 (a/sum-mono S4 WZ n 'we
                          (fn [v hv] (rmono (at z v) (vertex-price B y E v) (at w v) (at 'hz v hv) (at 'hdual v hv))))]
    (s/spec 'signed/incidence-cover-weak-duality
            (into [['B matrix] ['w family] ['y family] ['z family] ['n nat] ['E nat]
                   ['hy (s/all-below E #(le s/zero (at y %)))]
                   ['hdual (s/all-below n #(le (vertex-price B y E %) (at w %)))]]
                  (competitor-binders B z n E))
            (le Y (sum WZ n))
            (le-trans Y (sum S1 E) (sum WZ n) step1
                      (le-resp (sum S4 n) (sum S1 E) (sum WZ n) (sum WZ n)
                               (sym (sum S1 E) (sum S4 n) (a/chain (sum S1 E) [(sum S2 E) eq2] [(sum S3 n) eq3] [(sum S4 n) eq4]))
                               (refl (sum WZ n)) step5)))))

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

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec mmck/successor-positive-spec])

(def theorem-specs [weak-duality-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-associative/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      (support/extend-with-shared :expr-sum-weighted-cover-rounding theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
