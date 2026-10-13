(ns rainbow.math.lemmas.nmb-decision
  "General lemmas: nmb decision. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.rational.signed.no-zero-divisors :as positivity]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]))

(def type-level [:succ [:zero]])

(def one (f/const* 'signed/one []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn nonneg-prod [p q hp hq]
  (le-resp (mul p s/zero) s/zero (mul p q) (mul p q) (call 'signed/multiply-zero-right p) (refl (mul p q))
           (call 'signed/multiply-left-monotone p s/zero q hp hq)))

(defn gap-le [x y h]
  (le-resp (add (sub x y) y) x (add s/zero y) y (ring (add (sub x y) y) x) (ring (add s/zero y) y)
           (call 'signed/add-right-monotone (sub x y) s/zero y h)))

(defn le-gap [x y h]
  (le-resp (add x (neg x)) s/zero (add y (neg x)) (sub y x) (ring (add x (neg x)) s/zero) (refl (sub y x))
           (call 'signed/add-right-monotone x y (neg x) h)))

(defn weighted [w v n] (sum (f/lam [['wv-i nat]] (mul (at w 'wv-i) (at v 'wv-i))) n))

(def attains-spec
  (let [sv 'sa-s v 'sa-v n 'sa-n B 'sa-b
        T (f/lam [['sa-t nat]] (mul (at sv 'sa-t) (sub B (at v 'sa-t))))
        T2 (f/lam [['sa-u nat]] (sub (mul (at sv 'sa-u) B) (mul (at sv 'sa-u) (at v 'sa-u))))
        SB (f/lam [['sa-w nat]] (mul (at sv 'sa-w) B))
        SV (f/lam [['wv-i nat]] (mul (at sv 'wv-i) (at v 'wv-i)))
        total (a/chain (sum T n)
                       [(sum T2 n) (a/sum-cong T T2 n 'sa-c (fn [i _] (ring (mul (at sv i) (sub B (at v i))) (sub (mul (at sv i) B) (mul (at sv i) (at v i))))))]
                       [(sub (sum SB n) (sum SV n)) (call 'signed/expr-sum-value-subtract SB SV n)]
                       [(sub (mul (sum sv n) B) B)
                        (s/add-cong (sum SB n) (mul (sum sv n) B) (neg (sum SV n)) (neg B)
                                    (sym (mul (sum sv n) B) (sum SB n) (call 'signed/expr-sum-value-scale-right sv B n))
                                    (a/neg-cong (sum SV n) B (sym B (sum SV n) 'sa-hb)))]
                       [(sub (mul one B) B) (s/add-cong (mul (sum sv n) B) (mul one B) (neg B) (neg B) (mcong (sum sv n) one B B 'sa-sum (refl B)) (refl (neg B)))]
                       [s/zero (a/chain (sub (mul one B) B) [(sub B B) (s/add-cong (mul one B) B (neg B) (neg B) (call 'signed/multiply-one-left B) (refl (neg B)))]
                                        [s/zero (ring (sub B B) s/zero)])])
        tnn (f/lam [['sn-i nat] ['sn-h (below 'sn-i n)]]
                   (nonneg-prod (at sv 'sn-i) (sub B (at v 'sn-i)) (at 'sa-nn 'sn-i 'sn-h) (le-gap (at v 'sn-i) B (at 'sa-le 'sn-i 'sn-h))))
        each (call 'signed/expr-sum-value-nonnegative-terms-zero T n tnn total)
        goal (eqv (at v 'sa-i) B)]
    (s/spec 'signed/selection-attains
            [['sa-s family] ['sa-v family] ['sa-n nat] ['sa-b signed]
             ['sa-nn (s/all-below n #(le s/zero (at sv %)))] ['sa-sum (eqv (sum sv n) one)]
             ['sa-hb (eqv B (weighted sv v n))] ['sa-le (s/all-below n #(le (at v %) B))]
             ['sa-i nat] ['sa-hi (below 'sa-i n)] ['sa-nz (f/arrow (eqv (at sv 'sa-i) s/zero) falsity)]]
            goal
            (cases (eqv (at sv 'sa-i) s/zero) (eqv (sub B (at v 'sa-i)) s/zero) goal
                   (call 'signed/multiply-zero-split (at sv 'sa-i) (sub B (at v 'sa-i)) (at each 'sa-i 'sa-hi))
                   (f/lam [['sa-z (eqv (at sv 'sa-i) s/zero)]] (call 'proposition/explode goal (f/app 'sa-nz 'sa-z)))
                   (f/lam [['sa-g (eqv (sub B (at v 'sa-i)) s/zero)]]
                          (a/chain (at v 'sa-i) [(sub B (sub B (at v 'sa-i))) (ring (at v 'sa-i) (sub B (sub B (at v 'sa-i))))]
                                   [(sub B s/zero) (s/add-cong B B (neg (sub B (at v 'sa-i))) (neg s/zero) (refl B) (a/neg-cong (sub B (at v 'sa-i)) s/zero 'sa-g))]
                                   [B (ring (sub B s/zero) B)]))))))

(defn ge-gap [x y h]
  (le-resp (add s/zero x) x (add (sub y x) x) y (ring (add s/zero x) x) (ring (add (sub y x) x) y)
           (call 'signed/add-right-monotone s/zero (sub y x) x h)))

(defn icer-prop [l Ei Ej Ci Cj Ni Nj]
  (pconj (f/arrow (le Nj Ni) (le (sub Ci Cj) (mul l (sub Ei Ej))))
         (f/arrow (le (sub Ci Cj) (mul l (sub Ei Ej))) (le Nj Ni))))

(def icer-spec
  (let [[l Ei Ej Ci Cj Ni Nj] '[ic-l ic-ei ic-ej ic-ci ic-cj ic-ni ic-nj]
        lhs (sub Ci Cj) rhs (mul l (sub Ei Ej))
        diff (a/chain (sub Ni Nj)
                      [(sub (sub (mul l Ei) Ci) (sub (mul l Ej) Cj)) (s/add-cong Ni (sub (mul l Ei) Ci) (neg Nj) (neg (sub (mul l Ej) Cj)) 'ic-hi (a/neg-cong Nj (sub (mul l Ej) Cj) 'ic-hj))]
                      [(sub rhs lhs) (ring (sub (sub (mul l Ei) Ci) (sub (mul l Ej) Cj)) (sub rhs lhs))])
        fwd (f/lam [['ic-le (le Nj Ni)]]
                   (ge-gap lhs rhs (le-resp s/zero s/zero (sub Ni Nj) (sub rhs lhs) (refl s/zero) diff (le-gap Nj Ni 'ic-le))))
        bwd (f/lam [['ic-ge (le lhs rhs)]]
                   (ge-gap Nj Ni (le-resp s/zero s/zero (sub rhs lhs) (sub Ni Nj) (refl s/zero) (sym (sub Ni Nj) (sub rhs lhs) diff) (le-gap lhs rhs 'ic-ge))))]
    (s/spec 'signed/icer-rule
            [['ic-l signed] ['ic-ei signed] ['ic-ej signed] ['ic-ci signed] ['ic-cj signed] ['ic-ni signed] ['ic-nj signed]
             ['ic-hi (eqv Ni (sub (mul l Ei) Ci))] ['ic-hj (eqv Nj (sub (mul l Ej) Cj))]]
            (icer-prop l Ei Ej Ci Cj Ni Nj)
            (conjoin (f/arrow (le Nj Ni) (le lhs rhs)) (f/arrow (le lhs rhs) (le Nj Ni)) fwd bwd))))

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

(def theorem-specs [attains-spec icer-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      positivity/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      (support/extend-with-shared :expr-sum-nmb-decision theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
