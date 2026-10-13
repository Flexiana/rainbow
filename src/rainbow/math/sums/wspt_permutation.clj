(ns rainbow.math.sums.wspt-permutation
  "WSPT optimality over all permutation matrices, with positive processing times.
  Pairwise and prefix quantities use the existing expr-sum-value throughout."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum add mul le eqv refl sym]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.lemmas.assign-dual :as assignment]
            [rainbow.math.sums.permutation-invariant :as pi]
            [rainbow.math.sums.wspt-pair-bound :as pb]
            [rainbow.math.sums.wspt-order :as order]
            [rainbow.math.sums.triangular :as tr]))
(defn permutation [X n]
  (call 'proposition/conjunction (pi/binary-cells X n)
    (call 'proposition/conjunction (assignment/row-sums-one X n) (assignment/col-sums-one X n))))
(defn permutation-parts [X n h]
  (let [B (pi/binary-cells X n) R (assignment/row-sums-one X n) C (assignment/col-sums-one X n)
        rc (call 'proposition/right B (call 'proposition/conjunction R C) h)]
    {:bits (call 'proposition/left B (call 'proposition/conjunction R C) h)
     :rows (call 'proposition/left R C rc) :cols (call 'proposition/right R C rc)}))
(defn bits-nonnegative [X n bits]
  (f/lam [['pi-row nat] ['pi-rb (s/below 'pi-row n)] ['pi-col nat] ['pi-cb (s/below 'pi-col n)]]
    (let [v (at X 'pi-row 'pi-col) z (eqv v s/zero) o (eqv v a/one)]
      (a/cases z o (le s/zero v) (at bits 'pi-row 'pi-rb 'pi-col 'pi-cb)
        (f/lam [['wp-zero z]] (a/eq-le s/zero v (sym v s/zero 'wp-zero)))
        (f/lam [['wp-one o]]
          (s/le-transport s/zero s/zero a/one v (refl s/zero) (sym v a/one 'wp-one)
            (call 'signed/less-than-implies-at-most s/zero a/one (f/const* 'signed/zero-less-than-one []))))))))
(defn op-proof [G body]
  (f/lam [['pi-a signed] ['pi-b signed] ['pi-c signed] ['pi-d signed]
          ['pi-ac (eqv 'pi-a 'pi-c)] ['pi-bd (eqv 'pi-b 'pi-d)]] (body 'pi-a 'pi-b 'pi-c 'pi-d 'pi-ac 'pi-bd)))
(defn invariant [X P W G n respects perm]
  (let [{:keys [bits rows cols]} (permutation-parts X n perm)]
    (call 'signed/permutation-binary-operation-sum-invariant X P W G n respects
      (bits-nonnegative X n bits) bits rows cols)))
(def diagonal-spec
  (let [X 'wp-X P 'wp-P W 'wp-W n 'wp-n
        PX (pi/transformed X P n) WX (pi/transformed X W n)
        G (f/lam [['wp-a signed] ['wp-b signed]] (mul 'wp-a 'wp-b))]
    (s/spec 'signed/wspt-permutation-diagonal-invariant
      [[X pi/matrix] [P family] [W family] [n nat] ['wp-permutation (permutation X n)]]
      (eqv (tr/diagonal (tr/products PX WX) n) (tr/diagonal (tr/products P W) n))
      (invariant X P W G n
        (op-proof G (fn [v w vh wh hv hw] (a/mul-cong v vh w wh hv hw))) 'wp-permutation))))
(defn min-cong [a b c d ac bd] (call 'signed/wspt-min-respects-equivalence a b c d ac bd))
(def pair-spec
  (let [X 'wp-X P 'wp-P W 'wp-W n 'wp-n PX (pi/transformed X P n) WX (pi/transformed X W n)
        K (pb/pair-matrix P W) KX (pb/pair-matrix PX WX)
        H (f/lam [['wp-position nat] ['wp-job nat]]
            (pb/minimum (mul (at PX 'wp-position) (at W 'wp-job)) (mul (at P 'wp-job) (at WX 'wp-position))))
        F0 (f/lam [['wp-outer nat]] (sum (tr/row KX 'wp-outer) n))
        F1 (f/lam [['wp-outer nat]] (sum (tr/row H 'wp-outer) n))
        F2 (f/lam [['wp-job nat]] (sum (tr/column H 'wp-job) n))
        F3 (f/lam [['wp-job nat]] (sum (tr/column K 'wp-job) n))]
    (s/spec 'signed/wspt-permutation-pair-sum-invariant
      [[X pi/matrix] [P family] [W family] [n nat] ['wp-permutation (permutation X n)]]
      (eqv (tr/square KX n) (tr/square K n))
      (a/chain (tr/square KX n)
        [(tr/square H n)
         (a/sum-cong F0 F1 n 'wp-fixed-position
           (fn [h _]
             (let [ph (at PX h) wh (at WX h)
                   G (f/lam [['wp-a signed] ['wp-b signed]] (pb/minimum (mul ph 'wp-b) (mul 'wp-a wh)))]
               (invariant X P W G n
                 (op-proof G (fn [v w vh whh hv hw]
                   (min-cong (mul ph w) (mul v wh) (mul ph whh) (mul vh wh)
                     (a/mul-cong ph ph w whh (refl ph) hw)
                     (a/mul-cong v vh wh wh hv (refl wh))))) 'wp-permutation))))]
        [(sum F2 n) (call 'signed/expr-sum-value-swap H n n)]
        [(sum F3 n)
         (a/sum-cong F2 F3 n 'wp-fixed-job
           (fn [j _]
             (let [pj (at P j) wj (at W j)
                   G (f/lam [['wp-a signed] ['wp-b signed]] (pb/minimum (mul 'wp-a wj) (mul pj 'wp-b)))]
               (invariant X P W G n
                 (op-proof G (fn [v w vh wh hv hw]
                   (min-cong (mul v wj) (mul pj w) (mul vh wj) (mul pj wh)
                     (a/mul-cong v vh wj wj hv (refl wj))
                     (a/mul-cong pj pj w wh (refl pj) hw)))) 'wp-permutation))))]
        [(tr/square K n) (sym (tr/square K n) (sum F3 n) (call 'signed/expr-sum-value-swap K n n))]))))
(def positive-spec
  (let [X 'wp-X P 'wp-P n 'wp-n PX (pi/transformed X P n)
        {:keys [bits cols]} (permutation-parts X n 'wp-permutation)
        nn (bits-nonnegative X n bits)]
    (s/spec 'signed/wspt-permutation-processing-positive
      [[X pi/matrix] [P family] [n nat] ['wp-permutation (permutation X n)]
       ['wp-positive (order/positive-family P n)]]
      (order/positive-family PX n)
      (f/lam [['idx nat] ['bound (s/below 'idx n)]]
        (let [S (pi/column X 'idx) value (pi/selected-value X P n 'idx)
              result (order/lt s/zero value)
              picked (call 'signed/one-hot-selects S n
                       (f/lam [['wp-r nat] ['wp-rb (s/below 'wp-r n)]] (at nn 'wp-r 'wp-rb 'idx 'bound))
                       (f/lam [['wp-r nat] ['wp-rb (s/below 'wp-r n)]] (at bits 'wp-r 'wp-rb 'idx 'bound))
                       (at cols 'idx 'bound))]
          (at picked result
            (f/lam [['wp-picked nat] ['wp-proof (#'pi/selection S n 'wp-picked)]]
              (let [tail (call 'proposition/conjunction (eqv (at S 'wp-picked) a/one) (#'pi/reads S n 'wp-picked))
                    hb (call 'proposition/left (s/below 'wp-picked n) tail 'wp-proof)
                    rd (call 'proposition/right (eqv (at S 'wp-picked) a/one) (#'pi/reads S n 'wp-picked)
                         (call 'proposition/right (s/below 'wp-picked n) tail 'wp-proof))
                    pv (at P 'wp-picked)]
                (call 'signed/less-than-of-less-than-of-at-most s/zero pv value
                  (at 'wp-positive 'wp-picked hb) (a/eq-le pv value (sym value pv (at rd P))))))))))))
(defn expression-invariant [X P W n perm]
  (s/add-cong (tr/diagonal (tr/products (pi/transformed X P n) (pi/transformed X W n)) n)
    (tr/diagonal (tr/products P W) n)
    (tr/square (pb/pair-matrix (pi/transformed X P n) (pi/transformed X W n)) n)
    (tr/square (pb/pair-matrix P W) n)
    (call 'signed/wspt-permutation-diagonal-invariant X P W n perm)
    (call 'signed/wspt-permutation-pair-sum-invariant X P W n perm)))
(defn- twice-product [v]
  (let [two (add a/one a/one) product (mul v two)]
    (sym product (add v v)
      (a/chain product
        [(mul two v) (call 'signed/multiply-commutative v two)]
        [(add (mul a/one v) (mul a/one v)) (call 'signed/multiply-distributes-add-right a/one a/one v)]
        [(add v v) (s/add-cong (mul a/one v) v (mul a/one v) v
                     (call 'signed/multiply-one-left v) (call 'signed/multiply-one-left v))]))))
(def optimal-spec
  (let [X 'wp-X Y 'wp-Y P 'wp-P W 'wp-W q 'wp-count-predecessor n (s/succ q)
        PX (pi/transformed X P n) WX (pi/transformed X W n)
        PY (pi/transformed Y P n) WY (pi/transformed Y W n)
        FX (tr/completion-cost PX WX n) FY (tr/completion-cost PY WY n)
        AX (pb/pair-expression PX WX n) AY (pb/pair-expression PY WY n) A (pb/pair-expression P W n)
        pos (call 'signed/wspt-permutation-processing-positive X P n 'wp-X-permutation 'wp-positive)
        ordered (f/lam [['pb-later nat] ['pb-later-bound (s/below 'pb-later n)]
                        ['pb-earlier nat] ['pb-earlier-bound (s/below 'pb-earlier 'pb-later)]]
                  (let [i 'pb-earlier j 'pb-later]
                    (s/le-transport (mul (at WX j) (at PX i)) (mul (at PX i) (at WX j))
                      (mul (at WX i) (at PX j)) (mul (at PX j) (at WX i))
                      (call 'signed/multiply-commutative (at WX j) (at PX i))
                      (call 'signed/multiply-commutative (at WX i) (at PX j))
                      (call 'signed/wspt-adjacent-implies-pairwise PX WX q pos 'wp-adjacent i j
                        (call 'nat/at-most-transitive i (s/succ i) j (call 'nat/at-most-successor i) 'pb-earlier-bound)
                        'pb-later-bound))))
        same-X (s/trans AX A AY (expression-invariant X P W n 'wp-X-permutation)
                  (sym AY A (expression-invariant Y P W n 'wp-Y-permutation)))
        accepted (call 'signed/wspt-sorted-attains-pair-expression PX WX n ordered)
        twice (s/le-transport AY (add FX FX) (add FY FY) (add FY FY)
                (s/trans AY AX (add FX FX) (sym AX AY same-X) accepted) (refl (add FY FY))
                (call 'signed/wspt-pair-expression-lower-bound PY WY n))
        two (add a/one a/one)
        one-below-two (s/le-transport (add s/zero a/one) a/one two two
                        (s/trans (add s/zero a/one) (add a/one s/zero) a/one
                          (call 'signed/add-commutative s/zero a/one) (call 'signed/add-zero-right a/one)) (refl two)
                        (call 'signed/add-right-monotone s/zero a/one a/one
                          (call 'signed/less-than-implies-at-most s/zero a/one (f/const* 'signed/zero-less-than-one []))))]
    (s/spec 'signed/wspt-permutation-cost-optimal
      [[P family] [W family] [X pi/matrix] [Y pi/matrix] [q nat]
       ['wp-positive (order/positive-family P n)] ['wp-X-permutation (permutation X n)]
       ['wp-adjacent (order/adjacent PX WX q)] ['wp-Y-permutation (permutation Y n)]]
      (le FX FY)
      (call 'signed/multiply-positive-reflects-order FX FY two
        (call 'signed/less-than-of-less-than-of-at-most s/zero a/one two
          (f/const* 'signed/zero-less-than-one []) one-below-two)
        (s/le-transport (add FX FX) (mul FX two) (add FY FY) (mul FY two)
          (twice-product FX) (twice-product FY) twice)))))
(def theorem-specs [diagonal-spec pair-spec positive-spec optimal-spec])
(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[])

(defn install
  "Adds this module's own declarations."
  [env]
  (reduce (fn [checked spec] (println :wspt-permutation :installing (:name spec)) (flush) (support/add-spec-shared checked :expr-sum-wspt-permutation spec)) (-> env pi/extend-environment pb/extend-environment) theorem-specs))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.sums.wspt-permutation))
(defn theorem-ids [env] (support/spec-ids env theorem-specs))
