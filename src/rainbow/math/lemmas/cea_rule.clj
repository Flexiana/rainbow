(ns rainbow.math.lemmas.cea-rule
  "General lemmas: cea rule. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as f]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.sums.value-algebra :as s :refer [nat signed family call at sum mul le eqv refl sym trans below]]
            [rainbow.math.sums.flow-cut :as a]
            [rainbow.math.sums.nonneg-zero :as nonneg-zero]
            [rainbow.math.lemmas.indep-set-dual :as indep]
            [rainbow.math.rational.signed.decide-order :as decide]
            [rainbow.math.rational.signed.order-monotone :as add-monotone]
            [rainbow.math.rational.signed.multiply-ring :as multiply-ring]
            [rainbow.module :as module]))

(def type-level [:succ [:zero]])

(def prop-level [:zero])

(def one (f/const* 'signed/one []))

(def bool (f/const* 'data/Bool []))

(defn add [x y] (call 'signed/add x y))

(defn neg [x] (call 'signed/negate x))

(defn sub [x y] (a/sub x y))

(defn ring [x y] (a/ring-eq x y))

(defn le-resp [x xh y yh hx hy h] (call 'signed/at-most-respects-equivalence x xh y yh hx hy h))

(defn le-trans [x y z h k] (call 'signed/at-most-transitive x y z h k))

(defn le-refl [x] (call 'signed/at-most-reflexive x))

(defn anti [x y lo hi] (call 'signed/at-most-antisymmetric x y lo hi))

(defn eqb [x y] (f/equality type-level bool x y))

(def bfalse (f/const* 'data/false []))

(def btrue (f/const* 'data/true []))

(defn mn [c l t] (f/app (f/const* 'data/Bool.rec [type-level]) (f/lam [['ignored bool]] signed) l c t))

(defn dec [c l] (call 'signed/decide-at-most c l))

(defn award [c l] (mn c l (dec c l)))

(defn by-bit [D goal-of on-false on-true hname]
  (f/app (f/const* 'data/Bool.rec [prop-level])
         (f/lam [['bb bool]] (f/forall [[hname (eqb D 'bb)]] (goal-of 'bb)))
         (f/lam [[hname (eqb D bfalse)]] (on-false hname))
         (f/lam [[hname (eqb D btrue)]] (on-true hname))
         D
         (f/app (f/const* 'equality/reflexive [type-level]) bool D)))

(def min-left-spec
  (s/spec 'signed/decided-min-at-most-left [['c signed] ['l signed]]
          (le (award 'c 'l) 'c)
          (by-bit (dec 'c 'l) #(le (mn 'c 'l %) 'c)
                  (fn [h] (call 'signed/decide-at-most-false-reverse 'c 'l h))
                  (fn [_] (le-refl 'c))
                  'mh)))

(def min-level-spec
  (let [D1 (dec 'c 'l) D2 (dec 'c 'k)]
    (s/spec 'signed/decided-min-monotone-level [['c signed] ['l signed] ['k signed] ['h (le 'l 'k)]]
            (le (award 'c 'l) (award 'c 'k))
            (by-bit D1 #(le (mn 'c 'l %) (award 'c 'k))
                    (fn [h1] (by-bit D2 #(le 'l (mn 'c 'k %))
                                     (fn [_] 'h)
                                     (fn [_] (call 'signed/decide-at-most-false-reverse 'c 'l h1))
                                     'lh2))
                    (fn [h1] (by-bit D2 #(le 'c (mn 'c 'k %))
                                     (fn [_] (le-trans 'c 'l 'k (call 'signed/decide-at-most-true-sound 'c 'l h1) 'h))
                                     (fn [_] (le-refl 'c))
                                     'lh2))
                    'lh1))))

(def min-claim-spec
  (let [D1 (dec 'c 'l) D2 (dec 'd 'l)]
    (s/spec 'signed/decided-min-monotone-claim [['c signed] ['d signed] ['l signed] ['h (le 'c 'd)]]
            (le (award 'c 'l) (award 'd 'l))
            (by-bit D1 #(le (mn 'c 'l %) (award 'd 'l))
                    (fn [h1] (by-bit D2 #(le 'l (mn 'd 'l %))
                                     (fn [_] (le-refl 'l))
                                     (fn [_] (le-trans 'l 'c 'd (call 'signed/decide-at-most-false-reverse 'c 'l h1) 'h))
                                     'ch2))
                    (fn [h1] (by-bit D2 #(le 'c (mn 'd 'l %))
                                     (fn [_] (call 'signed/decide-at-most-true-sound 'c 'l h1))
                                     (fn [_] 'h)
                                     'ch2))
                    'ch1))))

(def termwise-spec
  (let [F 'F G 'G n 'n
        D (f/lam [['td nat]] (sub (at G 'td) (at F 'td)))
        d-nn (f/lam [['tn nat] ['tn-lt (below 'tn n)]]
                    (le-resp (add (at F 'tn) (neg (at F 'tn))) s/zero (add (at G 'tn) (neg (at F 'tn))) (sub (at G 'tn) (at F 'tn))
                             (ring (add (at F 'tn) (neg (at F 'tn))) s/zero) (refl (sub (at G 'tn) (at F 'tn)))
                             (call 'signed/add-right-monotone (at F 'tn) (at G 'tn) (neg (at F 'tn)) (at 'hle 'tn 'tn-lt))))
        d-sum (a/chain (sum D n)
                       [(sub (sum G n) (sum F n)) (call 'signed/expr-sum-value-subtract G F n)]
                       [(sub (sum F n) (sum F n)) (s/add-cong (sum G n) (sum F n) (neg (sum F n)) (neg (sum F n)) (sym (sum F n) (sum G n) 'hsum) (refl (neg (sum F n))))]
                       [s/zero (ring (sub (sum F n) (sum F n)) s/zero)])
        zero (call 'signed/expr-sum-value-nonnegative-terms-zero D n d-nn d-sum)]
    (s/spec 'signed/termwise-equal-of-equal-sums
            [['F family] ['G family] ['n nat] ['hle (s/all-below n #(le (at F %) (at G %)))] ['hsum (eqv (sum F n) (sum G n))]]
            (s/all-below n #(eqv (at F %) (at G %)))
            (f/lam [['ti nat] ['ti-lt (below 'ti n)]]
                   (let [Fi (at F 'ti) Gi (at G 'ti)]
                     (a/chain Fi [(add Fi (sub Gi Fi)) (sym (add Fi (sub Gi Fi)) Fi
                                                            (a/chain (add Fi (sub Gi Fi)) [(add Fi s/zero) (s/add-cong Fi Fi (sub Gi Fi) s/zero (refl Fi) (at zero 'ti 'ti-lt))]
                                                                     [Fi (call 'signed/add-zero-right Fi)]))]
                              [Gi (ring (add Fi (sub Gi Fi)) Gi)]))))))

(def unique-spec
  (let [c 'c d 'd x 'x y 'y l 'l k 'k E 'E Ey 'Ey n 'n
        dominate (fn [p q cp cq lp lq hl hcl hxp hxq]  ; lp <= lq, cp_i <= cq_i, p ~ award(cp, lp), q ~ award(cq, lq): p_i <= q_i
                   (f/lam [['ui nat] ['ui-lt (below 'ui n)]]
                          (le-resp (award (at cp 'ui) lp) (at p 'ui) (award (at cq 'ui) lq) (at q 'ui)
                                   (sym (at p 'ui) (award (at cp 'ui) lp) (at hxp 'ui 'ui-lt)) (sym (at q 'ui) (award (at cq 'ui) lq) (at hxq 'ui 'ui-lt))
                                   (le-trans (award (at cp 'ui) lp) (award (at cp 'ui) lq) (award (at cq 'ui) lq)
                                             (call 'signed/decided-min-monotone-level (at cp 'ui) lp lq hl)
                                             (call 'signed/decided-min-monotone-claim (at cp 'ui) (at cq 'ui) lq (hcl 'ui 'ui-lt))))))
        Sx (sum (f/lam [['sx nat]] (at x 'sx)) n) Sy (sum (f/lam [['sy nat]] (at y 'sy)) n)
        sums (a/chain Sx [E 'hEx] [Ey 'hE] [Sy (sym Sy Ey 'hEy)])
        goal (s/all-below n #(eqv (at x %) (at y %)))
        c-le-d (fn [i hi] (a/eq-le (at c i) (at d i) (at 'hc i hi)))
        d-le-c (fn [i hi] (a/eq-le (at d i) (at c i) (sym (at c i) (at d i) (at 'hc i hi))))]
    (s/spec 'signed/cea-award-unique
            [['c family] ['d family] ['x family] ['y family] ['l signed] ['k signed] ['E signed] ['Ey signed] ['n nat]
             ['hx (s/all-below n #(eqv (at x %) (award (at c %) l)))] ['hy (s/all-below n #(eqv (at y %) (award (at d %) k)))]
             ['hEx (eqv Sx E)] ['hEy (eqv Sy Ey)]
             ['hc (s/all-below n #(eqv (at c %) (at d %)))] ['hE (eqv E Ey)]]
            goal
            (call 'proposition/use-disjunction (le l k) (le k l) goal (call 'signed/at-most-total l k)
                  (f/lam [['lk (le l k)]]
                         (call 'signed/termwise-equal-of-equal-sums (f/lam [['sx nat]] (at x 'sx)) (f/lam [['sy nat]] (at y 'sy)) n
                               (dominate x y c d l k 'lk c-le-d 'hx 'hy) sums))
                  (f/lam [['kl (le k l)]]
                         (let [yx (call 'signed/termwise-equal-of-equal-sums (f/lam [['sy nat]] (at y 'sy)) (f/lam [['sx nat]] (at x 'sx)) n
                                        (dominate y x d c k l 'kl d-le-c 'hy 'hx) (sym Sx Sy sums))]
                           (f/lam [['vi nat] ['vi-lt (below 'vi n)]] (sym (at y 'vi) (at x 'vi) (at yx 'vi 'vi-lt)))))))))

(defn conjunction [xs]
  (if (= 1 (count xs)) (first xs) (call 'proposition/conjunction (first xs) (conjunction (rest xs)))))

(defn cascade [ps proof needed body tag]
  (let [top (apply max needed)]
    (letfn [(go [ps k t acc]
              (let [last? (= 1 (count ps))
                    acc (if (needed k)
                          (assoc acc k (if last? t (call 'proposition/left (first ps) (conjunction (rest ps)) t)))
                          acc)]
                (if (or last? (>= k top))
                  (body acc)
                  (let [rest-t (conjunction (rest ps)) v (symbol (str "casc-" tag "-" (inc k)))]
                    (f/app (f/lam [[v rest-t]] (go (rest ps) (inc k) v acc))
                           (call 'proposition/right (first ps) rest-t t))))))]
      (go ps 0 proof {}))))

(defn names [kind stem]
  ({:conditions (symbol "signed" (str "cea-conditions-" stem)) :accepted (symbol "signed" (str "cea-accepted-" stem))
    :compiled (symbol "clj" (str "compiled-cea-" stem))} kind))

(def borrowed-specs [indep/total-spec])

(def theorem-specs [min-left-spec min-level-spec min-claim-spec termwise-spec unique-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.sums.value-append rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.checks rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.nat.divmod rainbow.math.rational.signed.minmax rainbow.math.rational.signed.minmax-algebra rainbow.math.rational.signed.clamp rainbow.math.rational.signed.deviation-rows rainbow.math.rational.signed.absolute rainbow.math.rational.signed.absolute-algebra rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.add-associative rainbow.math.nat.semiring rainbow.math.nat.multiply-zero-split rainbow.math.rational.nnrat.multiply-zero-split rainbow.math.nat.monus rainbow.math.rational.nnrat.monus rainbow.math.rational.nnrat.add-zero-split rainbow.math.rational.nnrat.add-cancel-zero rainbow.math.finite.rational-argmax rainbow.math.rational.nnrat.order-total rainbow.math.rational.nnrat.multiply-difference-zero rainbow.math.linear.vector.norm-nonnegative rainbow.math.linear.vector.norm-zero-reflection rainbow.algorithms.proofs.counterfactual-distance-separation rainbow.algorithms.proofs.counterfactual-distance-laws rainbow.math.finite.matrix rainbow.math.linear.matrix.equivalence rainbow.math.linear.matrix.transpose rainbow.math.linear.matrix.transpose-equivalence rainbow.math.linear.matrix.multiply rainbow.math.linear.matrix.multiply-shape rainbow.math.linear.matrix.composable rainbow.math.linear.matrix.composable-multiply rainbow.math.linear.vector.additive-units rainbow.math.linear.vector.shape-cancellation rainbow.math.linear.vector.shape-map rainbow.math.linear.vector.shape-add rainbow.math.linear.vector.dot-additive rainbow.math.linear.vector.dot-bilinear rainbow.math.linear.vector.dot-negate rainbow.math.linear.vector.dot-subtract rainbow.math.linear.vector.dot-scale rainbow.math.linear.matrix.action-scale rainbow.math.rational.signed.multiply-nonzero rainbow.math.rational.signed.order-monotone rainbow.math.rational.signed.list-sum rainbow.math.rational.signed.multiply-monotone rainbow.math.rational.signed.map-sum-algebra rainbow.math.rational.signed.negate-additive rainbow.math.rational.signed.lp-objective-negate rainbow.math.nat.pair-index-inverse rainbow.math.sums.flow-cut rainbow.math.sums.nonneg-zero rainbow.math.rational.signed.multiply-ring])

(defn install
  "Adds this module's own declarations."
  [env]
  (-> env (support/extend-with-shared :expr-sum-cea-rule borrowed-specs) (support/extend-with-shared :expr-sum-cea-rule theorem-specs)))

(defn extend-environment [env]
  (module/install-module env 'rainbow.math.lemmas.cea-rule))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
