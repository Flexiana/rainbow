(ns rainbow.math.lemmas.wab-mean
  "General lemmas: wab mean. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.one-center :as center]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn gap-le [x y h]
  (le-resp (add (sub x y) y) x (add s/zero y) y (ring (add (sub x y) y) x) (ring (add s/zero y) y)
           (call 'signed/add-right-monotone (sub x y) s/zero y h)))

(defn moment [w a n] (sum (f/lam [['mo-i nat]] (mul (at w 'mo-i) (at a 'mo-i))) n))

(def upper-spec
  (let [w 'wu-w a 'wu-a n 'wu-n U 'wu-u c 'wu-c W 'wu-bigw Ws (sum w n)
        WU (f/lam [['wu-k nat]] (mul (at w 'wu-k) U))
        M (moment w a n)
        per (fn [i hi] (let [wi (at w i) ai (at a i)]
                         (gap-le (mul wi ai) (mul wi U)
                                 (le-resp (mul wi (sub ai U)) (sub (mul wi ai) (mul wi U)) s/zero s/zero
                                          (ring (mul wi (sub ai U)) (sub (mul wi ai) (mul wi U))) (refl s/zero) (at 'wu-b i hi)))))
        M-le (le-resp M M (sum WU n) (mul W U) (refl M)
                      (trans (sum WU n) (mul Ws U) (mul W U) (sym (mul Ws U) (sum WU n) (call 'signed/expr-sum-value-scale-right w U n))
                             (mcong Ws W U U (sym W Ws 'wu-hw) (refl U)))
                      (a/sum-mono (f/lam [['mo-i nat]] (mul (at w 'mo-i) (at a 'mo-i))) WU n 'wu-m per))]
    (s/spec 'signed/weighted-mean-upper
            [['wu-w family] ['wu-a family] ['wu-n nat] ['wu-u signed] ['wu-c signed] ['wu-bigw signed]
             ['wu-hw (eqv W Ws)] ['wu-hc (eqv (mul c W) M)] ['wu-pos (call 'signed/less-than s/zero W)]
             ['wu-b (s/all-below n #(le (mul (at w %) (sub (at a %) U)) s/zero))]]
            (le c U)
            (call 'signed/at-most-cancel-positive-right c U W 'wu-pos
                  (le-resp M (mul c W) (mul W U) (mul U W) (sym (mul c W) M 'wu-hc) (call 'signed/multiply-commutative W U) M-le)))))

(def lower-spec
  (let [w 'wl-w a 'wl-a n 'wl-n L 'wl-l c 'wl-c W 'wl-bigw Ws (sum w n)
        WL (f/lam [['wl-k nat]] (mul (at w 'wl-k) L))
        M (moment w a n)
        per (fn [i hi] (let [wi (at w i) ai (at a i)]
                         (gap-le (mul wi L) (mul wi ai)
                                 (le-resp (mul wi (sub L ai)) (sub (mul wi L) (mul wi ai)) s/zero s/zero
                                          (ring (mul wi (sub L ai)) (sub (mul wi L) (mul wi ai))) (refl s/zero) (at 'wl-b i hi)))))
        le-M (le-resp (sum WL n) (mul W L) M M
                      (trans (sum WL n) (mul Ws L) (mul W L) (sym (mul Ws L) (sum WL n) (call 'signed/expr-sum-value-scale-right w L n))
                             (mcong Ws W L L (sym W Ws 'wl-hw) (refl L)))
                      (refl M)
                      (a/sum-mono WL (f/lam [['mo-i nat]] (mul (at w 'mo-i) (at a 'mo-i))) n 'wl-m per))]
    (s/spec 'signed/weighted-mean-lower
            [['wl-w family] ['wl-a family] ['wl-n nat] ['wl-l signed] ['wl-c signed] ['wl-bigw signed]
             ['wl-hw (eqv W Ws)] ['wl-hc (eqv (mul c W) M)] ['wl-pos (call 'signed/less-than s/zero W)]
             ['wl-b (s/all-below n #(le (mul (at w %) (sub L (at a %))) s/zero))]]
            (le L c)
            (call 'signed/at-most-cancel-positive-right L c W 'wl-pos
                  (le-resp (mul W L) (mul L W) M (mul c W) (call 'signed/multiply-commutative W L) (sym (mul c W) M 'wl-hc) le-M)))))

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

(def theorem-specs [upper-spec lower-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      center/extend-environment
      decide-complete/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-wab-mean theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
