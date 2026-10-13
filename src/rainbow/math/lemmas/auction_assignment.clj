(ns rainbow.math.lemmas.auction-assignment
  "General lemmas: auction assignment. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-monotone :as multiply-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.math.rational.signed.distributive :as distributive]
            [rainbow.math.linear.matrix.action-scale :as matrix-scale]
            [rainbow.math.linear.vector.dot-negate :as dot-negate]
            [rainbow.math.lemmas.bottleneck-assignment :as bap :refer [permutation-binders row-sum col-sum]]))

(def type-level [:succ [:zero]])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lmono [c x y hc h] (call 'signed/multiply-left-monotone c x y hc h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn net-row [z a p n i] (sum (f/lam [['nk nat]] (mul (at z i 'nk) (sub (at a i 'nk) (at p 'nk)))) n))

(defn value [z a n] (sum (f/lam [['vi nat]] (sum (f/lam [['vk nat]] (mul (at z 'vi 'vk) (at a 'vi 'vk))) n)) n))

(defn psum [p n] (sum (f/lam [['ps nat]] (at p 'ps)) n))

(def net-sum-spec
  (let [z 'z a 'a p 'p n 'n
        ZA (fn [i] (f/lam [['za nat]] (mul (at z i 'za) (at a i 'za))))
        ZP (fn [i] (f/lam [['zp nat]] (mul (at z i 'zp) (at p 'zp))))
        T (f/lam [['ti nat] ['tk nat]] (mul (at z 'ti 'tk) (at p 'tk)))
        per-row (fn [i] (a/chain (net-row z a p n i)
                                 [(sum (f/lam [['nd nat]] (sub (at (ZA i) 'nd) (at (ZP i) 'nd))) n)
                                  (a/sum-cong (f/lam [['nk nat]] (mul (at z i 'nk) (sub (at a i 'nk) (at p 'nk)))) (f/lam [['nd nat]] (sub (at (ZA i) 'nd) (at (ZP i) 'nd))) n 'na
                                              (fn [k _] (call 'signed/multiply-subtract-expand (at z i k) (at a i k) (at p k))))]
                                 [(sub (sum (ZA i) n) (sum (ZP i) n)) (call 'signed/expr-sum-value-subtract (ZA i) (ZP i) n)]))
        rows (f/lam [['ri nat]] (net-row z a p n 'ri))
        VA (f/lam [['vi nat]] (sum (ZA 'vi) n))
        VP (f/lam [['wi nat]] (sum (ZP 'wi) n))
        prices (a/chain (sum VP n)
                        [(sum (f/lam [['pk nat]] (sum (f/lam [['pi nat]] (mul (at z 'pi 'pk) (at p 'pk))) n)) n) (call 'signed/expr-sum-value-swap T n n)]
                        [(sum (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) n)
                         (a/sum-cong (f/lam [['pk nat]] (sum (f/lam [['pi nat]] (mul (at z 'pi 'pk) (at p 'pk))) n)) (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) n 'nb
                                     (fn [k _] (sym (mul (col-sum z n k) (at p k)) (sum (f/lam [['pi nat]] (mul (at z 'pi k) (at p k))) n)
                                                    (call 'signed/expr-sum-value-scale-right (f/lam [['ci nat]] (at z 'ci k)) (at p k) n))))]
                        [(psum p n) (a/sum-cong (f/lam [['pc nat]] (mul (col-sum z n 'pc) (at p 'pc))) (f/lam [['ps nat]] (at p 'ps)) n 'nc
                                                (fn [k hk] (trans (mul (col-sum z n k) (at p k)) (mul one (at p k)) (at p k)
                                                                  (mcong (col-sum z n k) one (at p k) (at p k) (at 'hcol k hk) (refl (at p k))) (one-times (at p k)))))])]
    (s/spec 'signed/assignment-net-sum
            [['z matrix] ['a matrix] ['p family] ['n nat] ['hcol (s/all-below n #(eqv (col-sum z n %) one))]]
            (eqv (sum rows n) (sub (value z a n) (psum p n)))
            (a/chain (sum rows n)
                     [(sum (f/lam [['rd nat]] (sub (at VA 'rd) (at VP 'rd))) n) (a/sum-cong rows (f/lam [['rd nat]] (sub (at VA 'rd) (at VP 'rd))) n 'nrow (fn [i _] (per-row i)))]
                     [(sub (sum VA n) (sum VP n)) (call 'signed/expr-sum-value-subtract VA VP n)]
                     [(sub (value z a n) (psum p n)) (s/add-cong (sum VA n) (value z a n) (neg (sum VP n)) (neg (psum p n)) (refl (sum VA n)) (a/neg-cong (sum VP n) (psum p n) prices))]))))

(def near-optimal-spec
  (let [a 'a x 'x y 'y p 'p eps 'eps n 'n
        G (fn [i] (net-row x a p n i))
        bound (fn [i] (add (G i) eps))
        ;; row i of y: sum_k y_ik (a_ik - p_k) <= G_i + eps
        row-le (fn [i hi]
                 (let [Yl (f/lam [['yl nat]] (mul (at y i 'yl) (sub (at a i 'yl) (at p 'yl))))
                       Yr (f/lam [['yr nat]] (mul (at y i 'yr) (bound i)))]
                   (le-resp (sum Yl n) (net-row y a p n i) (sum Yr n) (bound i) (refl (sum Yl n))
                            (a/chain (sum Yr n) [(mul (row-sum y n i) (bound i)) (sym (mul (row-sum y n i) (bound i)) (sum Yr n) (call 'signed/expr-sum-value-scale-right (f/lam [['rj nat]] (at y i 'rj)) (bound i) n))]
                                     [(mul one (bound i)) (mcong (row-sum y n i) one (bound i) (bound i) (at 'hrow i hi) (refl (bound i)))]
                                     [(bound i) (one-times (bound i))])
                            (a/sum-mono Yl Yr n 'ra
                                        (fn [k hk] (lmono (at y i k) (sub (at a i k) (at p k)) (bound i)
                                                          (call 'signed/zero-one-nonnegative (at y i k) (at 'hy01 i hi k hk)) (at 'hcs i hi k hk)))))))
        Yrows (f/lam [['yo nat]] (net-row y a p n 'yo))
        Bounds (f/lam [['bo nat]] (bound 'bo))
        Gs (f/lam [['go nat]] (G 'go))
        E (f/lam [['eo nat]] eps)
        total-le (a/sum-mono Yrows Bounds n 'rb (fn [i hi] (row-le i hi)))
        VY (value y a n) VX (value x a n) P (psum p n) nE (mul eps (of-nat/of-nat n))
        bounds-eq (a/chain (sum Bounds n)
                           [(add (sum Gs n) (sum E n)) (call 'signed/expr-sum-value-add Gs E n)]
                           [(add (sub VX P) nE) (s/add-cong (sum Gs n) (sub VX P) (sum E n) nE
                                                            (call 'signed/assignment-net-sum x a p n 'hxcol) (call 'signed/expr-sum-constant-of-nat eps n))])
        core (le-resp (sum Yrows n) (sub VY P) (sum Bounds n) (add (sub VX P) nE)
                      (call 'signed/assignment-net-sum y a p n 'hcol) bounds-eq total-le)]
    (s/spec 'signed/auction-near-optimal
            (-> [['a matrix] ['x matrix] ['p family] ['eps signed] ['n nat]
                 ['hxcol (s/all-below n #(eqv (col-sum x n %) one))]
                 ['hcs (f/forall [['ci nat] ['ci-lt (below 'ci n)] ['ck nat] ['ck-lt (below 'ck n)]] (le (sub (at a 'ci 'ck) (at p 'ck)) (add (G 'ci) eps)))]
                 ['y matrix]]
                (into (permutation-binders y n)))
            (le VY (add VX nE))
            (le-resp (add (sub VY P) P) VY (add (add (sub VX P) nE) P) (add VX nE)
                     (ring (add (sub VY P) P) VY) (ring (add (add (sub VX P) nE) P) (add VX nE))
                     (call 'signed/add-right-monotone (sub VY P) (add (sub VX P) nE) P core)))))

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

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec indep/subtract-expand-spec])

(def theorem-specs [net-sum-spec near-optimal-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      a/extend-environment
      nonneg-zero/extend-environment
      add-monotone/extend-environment
      multiply-monotone/extend-environment
      multiply-ring/extend-environment
      distributive/extend-environment
      matrix-scale/extend-environment
      dot-negate/extend-environment
      of-nat/extend-environment
      pairs/extend-environment
      (support/extend-with-shared :expr-sum-auction-assignment theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
