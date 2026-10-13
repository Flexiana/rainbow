(ns rainbow.math.lemmas.borda
  "General lemmas: borda. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.two-terms :as two-terms]
            [rainbow.math.sums.of-nat :as of-nat]
            [rainbow.math.lemmas.cea-rule :as cea]
            [rainbow.math.lemmas.kmeans-nearest :as kmeans]
            [rainbow.math.lemmas.bb-leaf-bound :as rectangular-index]
            [rainbow.math.lemmas.bottleneck-assignment :as bap]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.lemmas.one-center :as center :refer [le-ind eq-ind]]
            [rainbow.math.rational.signed.decide-completeness :as decide-complete]
            [rainbow.math.rational.signed.one-hot-attained :as attained]
            [rainbow.math.nat.pair-index-inverse :as pairs]
            [rainbow.math.finite.rational-argmax :as argmax]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def matrix (f/arrow nat family))

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(def falsity (f/const* 'proposition/falsity []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn lt [x y] (call 'signed/less-than x y))

(defn cases [p q r h l k] (call 'proposition/use-disjunction p q r h l k))

(defn disj [p q] (call 'proposition/disjunction p q))

(defn inl [p q h] (call 'proposition/left-disjunct p q h))

(defn inr [p q h] (call 'proposition/right-disjunct p q h))

(defn pconj [p q] (call 'proposition/conjunction p q))

(defn conjoin [p q hp hq] (call 'proposition/conjoin p q hp hq))

(defn pleft [p q h] (call 'proposition/left p q h))

(defn pright [p q h] (call 'proposition/right p q h))

(defn mcong [p q r t h k] (a/mul-cong p q r t h k))

(defn one-times [x] (call 'signed/multiply-one-left x))

(defn explode [goal h] (call 'proposition/explode goal h))

(defn eqb [x y] (f/equality type-level bool x y))

(defn eqn [x y] (f/equality type-level nat x y))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(def zero-le-one (call 'signed/less-than-implies-at-most s/zero one (f/const* 'signed/zero-less-than-one [])))

(defn ofn [k] (of-nat/of-nat k))

(defn exists-nat [P] (f/app (f/const* 'proposition/existence [type-level]) nat P))

(defn witness [P w pf] (f/app (f/const* 'proposition/witness [type-level]) nat P w pf))

(defn sel [at-false at-true t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) at-false at-true t))

(defn by-bit [D goal-of on-false on-true hname]
  (f/app (f/const* 'data/Bool.rec [prop-level])
         (f/lam [['bb bool]] (f/forall [[hname (eqb D 'bb)]] (goal-of 'bb)))
         (f/lam [[hname (eqb D bfalse)]] (on-false hname))
         (f/lam [[hname (eqb D btrue)]] (on-true hname))
         D
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(defn zero-or-one [x] (disj (eqv x s/zero) (eqv x one)))

(def eq-ind-one-spec
  (let [p 'p c 'c]
    (s/spec 'signed/eq-indicator-one-of-equivalent [['p signed] ['c signed] ['h (eqv p c)]]
            (eqv (eq-ind p c) one)
            (by-bit (call 'signed/decide-at-most p c) #(eqv (mul (sel s/zero one %) (le-ind c p)) one)
                    (fn [h1] (explode (eqv (mul s/zero (le-ind c p)) one)
                                      (f/app (call 'signed/decide-at-most-false-sound p c h1) (a/eq-le p c 'h))))
                    (fn [_] (by-bit (call 'signed/decide-at-most c p) #(eqv (mul one (sel s/zero one %)) one)
                                    (fn [h2] (explode (eqv (mul one s/zero) one)
                                                      (f/app (call 'signed/decide-at-most-false-sound c p h2) (a/eq-le c p (sym p c 'h)))))
                                    (fn [_] (one-times one))
                                    'oh2))
                    'oh1))))

(def eq-ind-equiv-spec
  (let [p 'p c 'c I (eq-ind p c)]
    (s/spec 'signed/equivalent-of-eq-indicator-one [['p signed] ['c signed] ['h (eqv I one)]]
            (eqv p c)
            (cases (eqv I s/zero) (pconj (eqv I one) (eqv p c)) (eqv p c) (call 'signed/eq-indicator-cases p c)
                   (f/lam [['iz (eqv I s/zero)]]
                          (explode (eqv p c) (call 'signed/one-not-equivalent-zero (trans one I s/zero (sym I one 'h) 'iz))))
                   (f/lam [['io (pconj (eqv I one) (eqv p c))]] (pright (eqv I one) (eqv p c) 'io))))))

(def unit-sum-witness-spec
  (let [F 'F k 'k
        Z (f/lam [['zg nat]] s/zero)
        P (f/lam [['wi nat]] (pconj (below 'wi k) (eqv (at F 'wi) one)))
        Q (f/lam [['qi nat]] (pconj (below 'qi k) (pconj (eqv (at F 'qi) one) (eqv (at Z 'qi) s/zero))))
        hw (f/lam [['wn nat] ['wn-lt (below 'wn k)]]
                  (cases (eqv (at F 'wn) s/zero) (eqv (at F 'wn) one) (le s/zero (at F 'wn)) (at 'h01 'wn 'wn-lt)
                         (f/lam [['z0 (eqv (at F 'wn) s/zero)]] (a/eq-le s/zero (at F 'wn) (sym (at F 'wn) s/zero 'z0)))
                         (f/lam [['z1 (eqv (at F 'wn) one)]] (le-resp s/zero s/zero one (at F 'wn) (refl s/zero) (sym (at F 'wn) one 'z1) zero-le-one))))
        hg (f/lam [['gn nat] ['gn-lt (below 'gn k)]] (call 'signed/at-most-reflexive s/zero))
        FZ (f/lam [['fz nat]] (mul (at F 'fz) (at Z 'fz)))
        hzero (a/chain (sum FZ k)
                       [(sum Z k) (a/sum-cong FZ Z k 'uz (fn [i _] (call 'signed/multiply-zero-right (at F i))))]
                       [s/zero (call 'signed/expr-sum-value-zero k)])
        found (call 'signed/one-hot-attained F Z k hw 'h01 hg 'hsum hzero)]
    (s/spec 'signed/unit-sum-witness
            [['F family] ['k nat] ['h01 (s/all-below k #(zero-or-one (at F %)))] ['hsum (eqv (sum F k) one)]]
            (exists-nat P)
            (f/app found (exists-nat P)
                   (f/lam [['fi nat] ['fe (at Q 'fi)]]
                          (witness P 'fi (conjoin (below 'fi k) (eqv (at F 'fi) one)
                                                  (pleft (below 'fi k) (pconj (eqv (at F 'fi) one) (eqv s/zero s/zero)) 'fe)
                                                  (pleft (eqv (at F 'fi) one) (eqv s/zero s/zero)
                                                         (pright (below 'fi k) (pconj (eqv (at F 'fi) one) (eqv s/zero s/zero)) 'fe)))))))))

(def eq-ind-zero-or-one-spec
  (let [I (eq-ind 'p 'c)]
    (s/spec 'signed/eq-indicator-zero-or-one [['p signed] ['c signed]]
            (zero-or-one I)
            (cases (eqv I s/zero) (pconj (eqv I one) (eqv 'p 'c)) (zero-or-one I) (call 'signed/eq-indicator-cases 'p 'c)
                   (f/lam [['iz (eqv I s/zero)]] (inl (eqv I s/zero) (eqv I one) 'iz))
                   (f/lam [['io (pconj (eqv I one) (eqv 'p 'c))]] (inr (eqv I s/zero) (eqv I one) (pleft (eqv I one) (eqv 'p 'c) 'io)))))))

(def succ-gt-spec
  (let [x 'x]
    (s/spec 'signed/less-than-add-one [['x signed]]
            (lt x (add x one))
            (call 'signed/less-than-intro x (add x one)
                  (le-resp (add x s/zero) x (add x one) (add x one) (call 'signed/add-zero-right x) (refl (add x one))
                           (call 'signed/add-left-monotone s/zero one x zero-le-one))
                  (f/lam [['xe (eqv x (add x one))]]
                         (call 'signed/one-not-equivalent-zero
                               (a/chain one [(sub (add x one) x) (ring one (sub (add x one) x))]
                                        [(sub x x) (s/add-cong (add x one) x (neg x) (neg x) (sym x (add x one) 'xe) (refl (neg x)))]
                                        [s/zero (ring (sub x x) s/zero)])))))))

(def of-nat-lt-spec
  (let [claim (fn [K] (f/forall [['lk nat] ['lk-lt (below 'lk K)]] (lt (ofn 'lk) (ofn K))))]
    (s/spec 'signed/of-nat-strictly-increasing [['K nat]]
            (claim 'K)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['ok nat]] (claim 'ok))
                   (f/lam [['lk nat] ['lk-lt (below 'lk s/nz)]] (two-terms/impossible-bound 'lk 'lk-lt (lt (ofn 'lk) (ofn s/nz))))
                   (f/lam [['oj nat] ['oih (claim 'oj)]]
                          (let [J 'oj top (ofn (s/succ J))
                                step (call 'signed/less-than-of-less-than-of-at-most (ofn J) (add (ofn J) one) top (call 'signed/less-than-add-one (ofn J))
                                           (a/eq-le (add (ofn J) one) top (sym top (add (ofn J) one) (call 'signed/of-nat-successor J))))]
                            (f/lam [['lk nat] ['lk-lt (below 'lk (s/succ J))]]
                                   (two-terms/split-last 'lk 'lk-lt J (lt (ofn 'lk) top)
                                                         (f/lam [['le-eq (eqn 'lk J)]]
                                                                (f/app (f/const* 'equality/substitution [type-level]) nat J 'lk
                                                                       (f/app (f/const* 'equality/symmetric [type-level]) nat 'lk J 'le-eq)
                                                                       (f/lam [['st nat]] (lt (ofn 'st) top)) step))
                                                         (f/lam [['le-lt (below 'lk J)]]
                                                                (call 'signed/less-than-transitive (ofn 'lk) (ofn J) top (at 'oih 'lk 'le-lt) step))))))
                   'K))))

(def at-most-one-spec
  (let [x 'x
        I (fn [k] (eq-ind x (ofn k)))
        Ifam (f/lam [['ik nat]] (I 'ik))
        claim (fn [K] (le (sum Ifam K) one))]
    (s/spec 'signed/literal-indicators-at-most-one [['x signed] ['K nat]]
            (claim 'K)
            (f/app (f/const* 'data/Nat.rec [prop-level])
                   (f/lam [['ak nat]] (claim 'ak))
                   zero-le-one
                   (f/lam [['aj nat] ['aih (claim 'aj)]]
                          (let [J 'aj SJ (sum Ifam J) IJ (I J) goal (le (add SJ IJ) one)]
                            (cases (eqv IJ s/zero) (pconj (eqv IJ one) (eqv x (ofn J))) goal (call 'signed/eq-indicator-cases x (ofn J))
                                   (f/lam [['jz (eqv IJ s/zero)]]
                                          (le-resp SJ (add SJ IJ) one one
                                                   (a/chain SJ [(add SJ s/zero) (sym (add SJ s/zero) SJ (call 'signed/add-zero-right SJ))]
                                                            [(add SJ IJ) (s/add-cong SJ SJ s/zero IJ (refl SJ) (sym IJ s/zero 'jz))])
                                                   (refl one) 'aih))
                                   (f/lam [['jo (pconj (eqv IJ one) (eqv x (ofn J)))]]
                                          (let [xJ (pright (eqv IJ one) (eqv x (ofn J)) 'jo)
                                                ;; every earlier indicator is 0: x ~ k ~ J contradicts k < J
                                                earlier (fn [k hk]
                                                          (cases (eqv (I k) s/zero) (pconj (eqv (I k) one) (eqv x (ofn k))) (eqv (I k) s/zero) (call 'signed/eq-indicator-cases x (ofn k))
                                                                 (f/lam [['ez (eqv (I k) s/zero)]] 'ez)
                                                                 (f/lam [['eo (pconj (eqv (I k) one) (eqv x (ofn k)))]]
                                                                        (explode (eqv (I k) s/zero)
                                                                                 (f/app (pright (call 'signed/at-most (ofn k) (ofn J)) (call 'proposition/negation (eqv (ofn k) (ofn J)))
                                                                                                (call 'signed/of-nat-strictly-increasing J k hk))
                                                                                        (trans (ofn k) x (ofn J) (sym x (ofn k) (pright (eqv (I k) one) (eqv x (ofn k)) 'eo)) xJ))))))
                                                s-zero (a/chain SJ [(sum (f/lam [['zk nat]] s/zero) J) (a/sum-cong Ifam (f/lam [['zk nat]] s/zero) J 'az (fn [k hk] (earlier k hk)))]
                                                                [s/zero (call 'signed/expr-sum-value-zero J)])]
                                            (a/eq-le (add SJ IJ) one
                                                     (a/chain (add SJ IJ) [(add s/zero one) (s/add-cong SJ s/zero IJ one s-zero (pleft (eqv IJ one) (eqv x (ofn J)) 'jo))]
                                                              [one (ring (add s/zero one) one)])))))))
                   'K))))

(defn holder-pred [R v k mm] (f/lam [['ec nat]] (pconj (below 'ec mm) (eqv (at R v 'ec) (ofn k)))))

(defn rank-pred [R v c mm] (f/lam [['ek nat]] (pconj (below 'ek mm) (eqv (at R v c) (ofn 'ek)))))

(defn winner-pred [S W mm] (f/lam [['pw nat]] (pconj (below 'pw mm) (pconj (eqv (at W 'pw) one) (s/all-below mm #(le (at S %) (at S 'pw)))))))

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

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn subst-nat [x y h P px] (f/app (f/const* 'equality/substitution [type-level]) nat x y h P px))

(defn m [] (s/succ 'q))

(defn holders [R v k] (f/lam [['hc nat]] (eq-ind (at R v 'hc) (ofn k))))

(defn rank-count [G R v k hv hk]
  (let [mm (m) g (call 'algebra/nat-add k (call 'nat/multiply v mm))
        hg (call 'nat/pair-index-below-rectangular mm k v 'V hk hv)
        rowg (call 'nat/row-of mm g) colg (call 'nat/col-of mm g)
        cnt (fn [vv kk] (sum (holders R vv kk) mm))
        lo (subst-nat colg k (call 'nat/col-of-pair-index mm k v hk) (f/lam [['sk nat]] (le (cnt v 'sk) one))
                      (subst-nat rowg v (call 'nat/row-of-pair-index mm k v hk) (f/lam [['sv nat]] (le (cnt 'sv colg) one)) (at (G 0) g hg)))
        hi (subst-nat colg k (call 'nat/col-of-pair-index mm k v hk) (f/lam [['sk nat]] (le one (cnt v 'sk)))
                      (subst-nat rowg v (call 'nat/row-of-pair-index mm k v hk) (f/lam [['sv nat]] (le one (cnt 'sv colg))) (at (G 1) g hg)))]
    (anti (cnt v k) one lo hi)))

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "borda-conditions-" stem)) :accepted (symbol "signed" (str "borda-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-borda-" stem))} kind))

(defn vk-binders [] [['v nat] ['v-lt (below 'v 'V)] ['k nat] ['k-lt (below 'k (m))]])

(def borrowed-specs [kmeans/zero-one-nonneg-spec rectangular-index/rectangular-spec two-terms/two-distinct-bound-spec
                     cea/termwise-spec bap/no-successor-below-spec indep/subtract-expand-spec])

(def theorem-specs [eq-ind-one-spec eq-ind-equiv-spec unit-sum-witness-spec eq-ind-zero-or-one-spec succ-gt-spec of-nat-lt-spec at-most-one-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env center/extend-environment of-nat/extend-environment decide-complete/extend-environment attained/extend-environment pairs/extend-environment two-terms/extend-environment argmax/extend-environment (support/extend-with-shared :expr-sum-borda borrowed-specs) (support/extend-with-shared :expr-sum-borda theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.borda))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
