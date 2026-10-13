(ns rainbow.algorithms.proofs.graph.dijkstra-invariant
  "DIJKSTRA'S INVARIANT (the Dijkstra step family's Level-3 half).
  Labels L(t, v), settled flags s(t, v) that are 0 or 1 (settled when s ~ 1), chosen nodes p t,
  and NONNEGATIVE weights W on n nodes. Each iteration satisfies (from
  signed/dijkstra-step-reading):

     R1 p < n    R2 s(t, p) ~ 0    R3 s(t, j) ~ 0 -> L(t, p) <= L(t, j)          (argmin of the unsettled)
     R4 s(t+1, j) ~ 1 -> s(t, j) ~ 1 \\/ j = p     R5 s(t+1, j) ~ 0 -> s(t, j) ~ 0 /\\ j /= p
     R6 L(t+1, j) <= L(t, j)    R7 L(t+1, j) <= L(t, p) + W(p, j)
     R8 L(t+1, j) ~ L(t, j) \\/ L(t+1, j) ~ L(t, p) + W(p, j)

  The invariant, for every t reached through such rounds from a start with nothing settled and
  L(0, 0) <= 0:

     A  settled u: L(t, u) <= the length of every walk 0 -> u        (settled labels are final)
     C  settled u: L(t, v) <= L(t, u) + W(u, v) for every v           (their arcs are relaxed)
     D  settled u, unsettled v: L(t, u) <= L(t, v)                    (settled below unsettled)
     S  L(t, 0) <= 0

  signed/dijkstra-walk-bound, derived from C by induction on the walk: every walk from 0 whose nodes
  before the last are settled bounds the label at its end. The new node's label is FINAL: a walk to
  p first leaves the settled set at some x f (nat/least-witness), and
  L(t, p) <= L(t, x f) <= prefix <= whole walk, by argmin, the walk bound and nonnegative weights.
  Settled labels never change (R8 with W >= 0 and D), which keeps C."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.proposition :as proposition]
            [rainbow.math.nat.extremal-index :as extremal]
            [rainbow.algorithms.proofs.graph.walk-cycle-cut :as cycle-cut]
            [rainbow.math.sums.value-append :as append]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private signed (function/const* 'signed/SignedRational []))
(def ^:private szero (function/const* 'signed/zero []))
(def ^:private sone (function/const* 'signed/one []))
(def ^:private grid-type (function/arrow nat (function/arrow nat signed)))
(def ^:private walk-type (function/arrow nat nat))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- signed-add [a b] (app (function/const* 'signed/add []) a b))
(defn- sle [a b] (app (function/const* 'signed/at-most []) a b))
(defn- sequiv [a b] (app (function/const* 'signed/equivalent []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- nat-refl [a] (app (function/const* 'equality/reflexive [type-level]) nat a))
(defn- nat-sym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))
(defn- sb-self [m] (app (function/const* 'nat/strict-below-self []) m))
(defn- falsity [] (function/const* 'proposition/falsity []))
(defn- not* [P] (function/arrow P (falsity)))
(defn- conj* [l r] (proposition/conjunction l r))
(defn- conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))
(defn- pleft [l r both] (app (function/const* 'proposition/left []) l r both))
(defn- pright [l r both] (app (function/const* 'proposition/right []) l r both))
(defn- disj* [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))
(defn- equiv-refl [a] (app (function/const* 'signed/equivalent-reflexive []) a))
(defn- equiv-sym [a b h] (app (function/const* 'signed/equivalent-symmetric []) a b h))
(defn- equiv-trans [a b c h1 h2] (app (function/const* 'signed/equivalent-transitive []) a b c h1 h2))
(defn- le-respects [a ah b bh e1 e2 h] (app (function/const* 'signed/at-most-respects-equivalence []) a ah b bh e1 e2 h))
(defn- le-trans [a b c h1 h2] (app (function/const* 'signed/at-most-transitive []) a b c h1 h2))
(defn- le-refl [a] (app (function/const* 'signed/at-most-reflexive []) a))
(defn- add-zero-right [a] (app (function/const* 'signed/add-zero-right []) a))

(defn- L-at [L t v] (app L t v))
(defn- s-at [s t v] (app s t v))
(defn- settled [s t v] (sequiv (s-at s t v) sone))
(defn- unsettled [s t v] (sequiv (s-at s t v) szero))
(defn- arc-weights [W x] (function/lam [['ta nat]] (app W (app x 'ta) (app x (succ 'ta)))))
(defn- walk-length [W x k] (expr-sum-value (arc-weights W x) k))
(defn- in-range [n x k] (function/forall [['tr nat] ['htr (at-most 'tr k)]] (strict-below (app x 'tr) n)))

(defn- both-absurd
  "s ~ 0 and s ~ 1 |- anything"
  [v h0 h1 P]
  (explode P (app (function/const* 'signed/one-not-equivalent-zero []) (equiv-trans sone v szero (equiv-sym v sone h1) h0))))

;; ---------------------------------------------------------------------------------------------
;; (b): walks whose nodes before the last are settled

(defn- relaxed-prop [n W L s t]
  (function/forall [['u nat] ['hu (strict-below 'u n)] ['hsu (settled s t 'u)] ['v nat] ['hv (strict-below 'v n)]]
                   (sle (L-at L t 'v) (signed-add (L-at L t 'u) (app W 'u 'v)))))
(defn- prefix-settled [s t x k] (function/forall [['ps nat] ['hps (strict-below 'ps k)]] (settled s t (app x 'ps))))
(defn- walk-bound-claim [n W L s t x k]
  (function/forall [['hin (in-range n x k)] ['hset (prefix-settled s t x k)]]
                   (sle (L-at L t (app x k)) (walk-length W x k))))

(def walk-bound-spec
  {:name 'signed/dijkstra-walk-bound :universes []
   :type (function/forall [['n nat] ['W grid-type] ['L grid-type] ['s grid-type] ['t nat]
                           ['hc (relaxed-prop 'n 'W 'L 's 't)] ['hsrc (sle (L-at 'L 't nat-zero) szero)]
                           ['x walk-type] ['hx0 (eq-nat (app 'x nat-zero) nat-zero)] ['k nat]]
                          (walk-bound-claim 'n 'W 'L 's 't 'x 'k))
   :value
   (function/lam
    [['n nat] ['W grid-type] ['L grid-type] ['s grid-type] ['t nat]
     ['hc (relaxed-prop 'n 'W 'L 's 't)] ['hsrc (sle (L-at 'L 't nat-zero) szero)]
     ['x walk-type] ['hx0 (eq-nat (app 'x nat-zero) nat-zero)] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['kk nat]] (walk-bound-claim 'n 'W 'L 's 't 'x 'kk))
         ;; k = 0: L(t, x 0) = L(t, 0) <= 0 = length
         (function/lam [['hin (in-range 'n 'x nat-zero)] ['hset (prefix-settled 's 't 'x nat-zero)]]
                       (subst-nat nat-zero (app 'x nat-zero) (nat-sym (app 'x nat-zero) nat-zero 'hx0)
                                  (function/lam [['z0 nat]] (sle (L-at 'L 't 'z0) szero)) 'hsrc))
         ;; k + 1: L(t, x (k+1)) <= L(t, x k) + W(x k, x (k+1)) <= len k + W = len (k+1)
         (function/lam
          [['k nat] ['ih (walk-bound-claim 'n 'W 'L 's 't 'x 'k)]
           ['hin (in-range 'n 'x (succ 'k))] ['hset (prefix-settled 's 't 'x (succ 'k))]]
          (let [k1 (succ 'k) xk (app 'x 'k) xk1 (app 'x k1)
                hin-k (function/lam [['tr nat] ['htr (at-most 'tr 'k)]] (app 'hin 'tr (amt 'tr 'k k1 'htr (at-most-succ 'k))))
                hset-k (function/lam [['ps nat] ['hps (strict-below 'ps 'k)]] (app 'hset 'ps (app (function/const* 'nat/strict-below-weaken []) 'ps 'k 'hps)))
                before (app 'ih hin-k hset-k)
                w (app 'W xk xk1) len (walk-length 'W 'x 'k)
                relax (app 'hc xk (app 'hin 'k (at-most-succ 'k)) (app 'hset 'k (sb-self 'k)) xk1 (app 'hin k1 (at-most-refl k1)))]
            (le-trans (L-at 'L 't xk1) (signed-add (L-at 'L 't xk) w) (signed-add len w) relax
                      (app (function/const* 'signed/add-right-monotone []) (L-at 'L 't xk) len w before))))
         'k))})


;; ---------------------------------------------------------------------------------------------
;; one iteration: hypotheses and invariant parts

(defn- nonneg-weights [n W] (function/forall [['wu nat] ['hwu (strict-below 'wu n)] ['wv nat] ['hwv (strict-below 'wv n)]] (sle szero (app W 'wu 'wv))))
(defn- zero-one-at [n s t] (function/forall [['zv nat] ['hzv (strict-below 'zv n)]] (disj* (unsettled s t 'zv) (settled s t 'zv))))
(defn- rounds [n W L s P t]
  (let [p (app P t) t1 (succ t)]
    [[:R1 (strict-below p n)]
     [:R2 (unsettled s t p)]
     [:R3 (function/forall [['j3 nat] ['hj3 (strict-below 'j3 n)] ['hu3 (unsettled s t 'j3)]] (sle (L-at L t p) (L-at L t 'j3)))]
     [:R4 (function/forall [['j4 nat] ['hj4 (strict-below 'j4 n)] ['hs4 (settled s t1 'j4)]] (disj* (settled s t 'j4) (eq-nat 'j4 p)))]
     [:R5 (function/forall [['j5 nat] ['hj5 (strict-below 'j5 n)] ['hu5 (unsettled s t1 'j5)]] (conj* (unsettled s t 'j5) (not* (eq-nat 'j5 p))))]
     [:R6 (function/forall [['j6 nat] ['hj6 (strict-below 'j6 n)]] (sle (L-at L t1 'j6) (L-at L t 'j6)))]
     [:R7 (function/forall [['j7 nat] ['hj7 (strict-below 'j7 n)]] (sle (L-at L t1 'j7) (signed-add (L-at L t p) (app W p 'j7))))]
     [:R8 (function/forall [['j8 nat] ['hj8 (strict-below 'j8 n)]] (disj* (sequiv (L-at L t1 'j8) (L-at L t 'j8)) (sequiv (L-at L t1 'j8) (signed-add (L-at L t p) (app W p 'j8)))))]]))
(defn- round-binders [n W L s P t] (mapv (fn [[k prop]] [(symbol (str "h" (name k))) prop]) (rounds n W L s P t)))
(defn- rh [k] (symbol (str "h" (name k))))

(defn- final-prop [n W L s t]
  (function/forall [['fu nat] ['hfu (strict-below 'fu n)] ['hsf (settled s t 'fu)] ['fk nat] ['fx walk-type]
                    ['hf0 (eq-nat (app 'fx nat-zero) nat-zero)] ['hfin (in-range n 'fx 'fk)] ['hfk (eq-nat (app 'fx 'fk) 'fu)]]
                   (sle (L-at L t 'fu) (walk-length W 'fx 'fk))))
(defn- order-prop [n L s t]
  (function/forall [['ou nat] ['hou (strict-below 'ou n)] ['hso (settled s t 'ou)] ['ov nat] ['hov (strict-below 'ov n)] ['huo (unsettled s t 'ov)]]
                   (sle (L-at L t 'ou) (L-at L t 'ov))))
(defn- source-prop [L t] (sle (L-at L t nat-zero) szero))

(defn- common-binders [] [['n nat] ['W grid-type] ['L grid-type] ['s grid-type] ['P walk-type] ['t nat] ['hW (nonneg-weights 'n 'W)]])

(defn- plus-nonneg
  "a <= a + w when 0 <= w"
  [a w hw]
  (le-respects (signed-add a szero) a (signed-add a w) (signed-add a w) (add-zero-right a) (equiv-refl (signed-add a w))
               (app (function/const* 'signed/add-left-monotone []) szero w a hw)))

(defn- p-of [] (app 'P 't))

;; STAB: settled at t (or the chosen node) keeps its label: L(t, u) <= L(t+1, u)
(def stable-spec
  {:name 'signed/dijkstra-stable :universes []
   :type (function/forall (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
                                [['hD (order-prop 'n 'L 's 't)] ['u nat] ['hu (strict-below 'u 'n)]
                                 ['hsu (disj* (settled 's 't 'u) (eq-nat 'u (app 'P 't)))]])
                          (sle (L-at 'L 't 'u) (L-at 'L (succ 't) 'u)))
   :value
   (function/lam
    (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
          [['hD (order-prop 'n 'L 's 't)] ['u nat] ['hu (strict-below 'u 'n)]
           ['hsu (disj* (settled 's 't 'u) (eq-nat 'u (app 'P 't)))]])
    (let [p (p-of) t1 (succ 't) Lu (L-at 'L 't 'u) Lu1 (L-at 'L t1 'u) Lp (L-at 'L 't p) wpu (app 'W p 'u)
          goal (sle Lu Lu1)
          ;; L(t, u) <= L(t, p): settled u (order) or u = p
          u-le-p (use-disj (settled 's 't 'u) (eq-nat 'u p) (sle Lu Lp) 'hsu
                           (function/lam [['hs-st (settled 's 't 'u)]] (app 'hD 'u 'hu 'hs-st p (rh :R1) (rh :R2)))
                           (function/lam [['he-st (eq-nat 'u p)]]
                                         (subst-nat 'u p 'he-st (function/lam [['z-st nat]] (sle Lu (L-at 'L 't 'z-st))) (le-refl Lu))))]
      (use-disj (sequiv Lu1 Lu) (sequiv Lu1 (signed-add Lp wpu)) goal (app (rh :R8) 'u 'hu)
                (function/lam [['hk-st (sequiv Lu1 Lu)]]
                              (le-respects Lu Lu Lu Lu1 (equiv-refl Lu) (equiv-sym Lu1 Lu 'hk-st) (le-refl Lu)))
                (function/lam [['hv-st (sequiv Lu1 (signed-add Lp wpu))]]
                              (le-respects Lu Lu (signed-add Lp wpu) Lu1 (equiv-refl Lu) (equiv-sym Lu1 (signed-add Lp wpu) 'hv-st)
                                           (le-trans Lu Lp (signed-add Lp wpu) u-le-p (plus-nonneg Lp wpu (app 'hW p (rh :R1) 'u 'hu))))))))})

(defn- cite-stable [u hu hsu]
  (app (function/const* 'signed/dijkstra-stable []) 'n 'W 'L 's 'P 't 'hW (rh :R1) (rh :R2) (rh :R3) (rh :R4) (rh :R5) (rh :R6) (rh :R7) (rh :R8) 'hD u hu hsu))

(def relaxed-step-spec
  {:name 'signed/dijkstra-relaxed-step :universes []
   :type (function/forall (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
                                [['hC (relaxed-prop 'n 'W 'L 's 't)] ['hD (order-prop 'n 'L 's 't)]])
                          (relaxed-prop 'n 'W 'L 's (succ 't)))
   :value
   (function/lam
    (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
          [['hC (relaxed-prop 'n 'W 'L 's 't)] ['hD (order-prop 'n 'L 's 't)]])
    (function/lam
     [['u nat] ['hu (strict-below 'u 'n)] ['hsu (settled 's (succ 't) 'u)] ['v nat] ['hv (strict-below 'v 'n)]]
     (let [p (p-of) t1 (succ 't) goal (sle (L-at 'L t1 'v) (signed-add (L-at 'L t1 'u) (app 'W 'u 'v)))
           either (app (rh :R4) 'u 'hu 'hsu)
           stab (cite-stable 'u 'hu either)]
       (use-disj (settled 's 't 'u) (eq-nat 'u p) goal either
                 ;; settled at t: L(t+1, v) <= L(t, v) <= L(t, u) + W <= L(t+1, u) + W
                 (function/lam
                  [['hs-rs (settled 's 't 'u)]]
                  (le-trans (L-at 'L t1 'v) (L-at 'L 't 'v) (signed-add (L-at 'L t1 'u) (app 'W 'u 'v))
                            (app (rh :R6) 'v 'hv)
                            (le-trans (L-at 'L 't 'v) (signed-add (L-at 'L 't 'u) (app 'W 'u 'v)) (signed-add (L-at 'L t1 'u) (app 'W 'u 'v))
                                      (app 'hC 'u 'hu 'hs-rs 'v 'hv)
                                      (app (function/const* 'signed/add-right-monotone []) (L-at 'L 't 'u) (L-at 'L t1 'u) (app 'W 'u 'v) stab))))
                 ;; the chosen node: L(t+1, v) <= L(t, p) + W(p, v) <= L(t+1, p) + W(p, v)
                 (function/lam
                  [['he-rs (eq-nat 'u p)]]
                  (subst-nat p 'u (nat-sym 'u p 'he-rs)
                             (function/lam [['z-rs nat]] (sle (L-at 'L t1 'v) (signed-add (L-at 'L t1 'z-rs) (app 'W 'z-rs 'v))))
                             (le-trans (L-at 'L t1 'v) (signed-add (L-at 'L 't p) (app 'W p 'v)) (signed-add (L-at 'L t1 p) (app 'W p 'v))
                                       (app (rh :R7) 'v 'hv)
                                       (app (function/const* 'signed/add-right-monotone []) (L-at 'L 't p) (L-at 'L t1 p) (app 'W p 'v)
                                            (cite-stable p (rh :R1) (app (function/const* 'proposition/right-disjunct []) (settled 's 't p) (eq-nat p p) (nat-refl p)))))))))))})

(def order-step-spec
  {:name 'signed/dijkstra-order-step :universes []
   :type (function/forall (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't)) [['hD (order-prop 'n 'L 's 't)]])
                          (order-prop 'n 'L 's (succ 't)))
   :value
   (function/lam
    (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't)) [['hD (order-prop 'n 'L 's 't)]])
    (function/lam
     [['u nat] ['hu (strict-below 'u 'n)] ['hsu (settled 's (succ 't) 'u)] ['v nat] ['hv (strict-below 'v 'n)] ['huv (unsettled 's (succ 't) 'v)]]
     (let [p (p-of) t1 (succ 't) Lp (L-at 'L 't p)
           v-then (pleft (unsettled 's 't 'v) (not* (eq-nat 'v p)) (app (rh :R5) 'v 'hv 'huv))
           ;; L(t, p) <= L(t+1, v)
           lower (use-disj (sequiv (L-at 'L t1 'v) (L-at 'L 't 'v)) (sequiv (L-at 'L t1 'v) (signed-add Lp (app 'W p 'v))) (sle Lp (L-at 'L t1 'v))
                           (app (rh :R8) 'v 'hv)
                           (function/lam [['hk-os (sequiv (L-at 'L t1 'v) (L-at 'L 't 'v))]]
                                         (le-respects Lp Lp (L-at 'L 't 'v) (L-at 'L t1 'v) (equiv-refl Lp) (equiv-sym (L-at 'L t1 'v) (L-at 'L 't 'v) 'hk-os)
                                                      (app (rh :R3) 'v 'hv v-then)))
                           (function/lam [['hv-os (sequiv (L-at 'L t1 'v) (signed-add Lp (app 'W p 'v)))]]
                                         (le-respects Lp Lp (signed-add Lp (app 'W p 'v)) (L-at 'L t1 'v) (equiv-refl Lp) (equiv-sym (L-at 'L t1 'v) (signed-add Lp (app 'W p 'v)) 'hv-os)
                                                      (plus-nonneg Lp (app 'W p 'v) (app 'hW p (rh :R1) 'v 'hv)))))
           ;; L(t+1, u) <= L(t, p)
           upper (use-disj (settled 's 't 'u) (eq-nat 'u p) (sle (L-at 'L t1 'u) Lp) (app (rh :R4) 'u 'hu 'hsu)
                           (function/lam [['hs-os (settled 's 't 'u)]]
                                         (le-trans (L-at 'L t1 'u) (L-at 'L 't 'u) Lp (app (rh :R6) 'u 'hu) (app 'hD 'u 'hu 'hs-os p (rh :R1) (rh :R2))))
                           (function/lam [['he-os (eq-nat 'u p)]]
                                         (subst-nat p 'u (nat-sym 'u p 'he-os) (function/lam [['z-os nat]] (sle (L-at 'L t1 'z-os) Lp)) (app (rh :R6) p (rh :R1)))))]
       (le-trans (L-at 'L t1 'u) Lp (L-at 'L t1 'v) upper lower))))})

(def source-step-spec
  {:name 'signed/dijkstra-source-step :universes []
   :type (function/forall (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't)) [['hS (source-prop 'L 't)]])
                          (source-prop 'L (succ 't)))
   :value
   (function/lam
    (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't)) [['hS (source-prop 'L 't)]])
    (let [p (p-of)
          zero-below (app (rh :R1) (strict-below nat-zero 'n)
                          (function/lam [['e-sr nat] ['pf-sr (eq-nat (nadd (succ p) 'e-sr) 'n)]]
                                        (app (function/const* 'proposition/witness [type-level]) nat
                                             (function/lam [['e2-sr nat]] (eq-nat (nadd (succ nat-zero) 'e2-sr) 'n)) (nadd p 'e-sr) 'pf-sr)))]
      (le-trans (L-at 'L (succ 't) nat-zero) (L-at 'L 't nat-zero) szero (app (rh :R6) nat-zero zero-below) 'hS)))})

(defn- prefix-le-whole
  "0 <= W on in-range arcs, f <= k  |-  walk-length(x, f) <= walk-length(x, k)"
  [n W x f k hW hin hfk]
  (app hfk (sle (walk-length W x f) (walk-length W x k))
       (function/lam
        [['e-pw nat] ['pe-pw (eq-nat (nadd f 'e-pw) k)]]
        (let [ek (app (function/const* 'equality/transitive [type-level]) nat (nadd 'e-pw f) (nadd f 'e-pw) k
                      (app (function/const* 'nat/add-commutative []) 'e-pw f) 'pe-pw)
              G (arc-weights W x) rest-f (function/lam [['i-pw nat]] (app G (nadd 'i-pw f)))
              rest (expr-sum-value rest-f 'e-pw)
              zero-f (function/lam [['z-pw nat]] szero)
              nonneg-terms (function/lam
                            [['i-pw nat] ['hi-pw (strict-below 'i-pw 'e-pw)]]
                            (let [a (nadd 'i-pw f)
                                  a1-le-k (subst-nat (nadd 'e-pw f) k ek (function/lam [['z-k nat]] (at-most (succ a) 'z-k))
                                                     (app (function/const* 'nat/add-right-monotone []) f (succ 'i-pw) 'e-pw 'hi-pw))]
                              (app hW (app x a) (app hin a (amt a (succ a) k (at-most-succ a) a1-le-k))
                                   (app x (succ a)) (app hin (succ a) a1-le-k))))
              rest-nonneg (le-respects (expr-sum-value zero-f 'e-pw) szero rest rest
                                       (app (function/const* 'signed/expr-sum-value-zero []) 'e-pw) (equiv-refl rest)
                                       (app (function/const* 'signed/expr-sum-value-monotone-below []) zero-f rest-f 'e-pw nonneg-terms))
              split (app (function/const* 'signed/expr-sum-value-append []) G f 'e-pw)      ; len(x, e+f) ~ len(x, f) + rest
              le-ef (le-respects (walk-length W x f) (walk-length W x f) (signed-add (walk-length W x f) rest) (walk-length W x (nadd 'e-pw f))
                                 (equiv-refl (walk-length W x f)) (equiv-sym (walk-length W x (nadd 'e-pw f)) (signed-add (walk-length W x f) rest) split)
                                 (plus-nonneg (walk-length W x f) rest rest-nonneg))]
          (subst-nat (nadd 'e-pw f) k ek (function/lam [['z-k nat]] (sle (walk-length W x f) (walk-length W x 'z-k))) le-ef)))))

(def final-step-spec
  {:name 'signed/dijkstra-final-step :universes []
   :type (function/forall (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
                                [['hA (final-prop 'n 'W 'L 's 't)] ['hC (relaxed-prop 'n 'W 'L 's 't)] ['hS (source-prop 'L 't)]
                                 ['h01 (zero-one-at 'n 's 't)]])
                          (final-prop 'n 'W 'L 's (succ 't)))
   :value
   (function/lam
    (into (into (common-binders) (round-binders 'n 'W 'L 's 'P 't))
          [['hA (final-prop 'n 'W 'L 's 't)] ['hC (relaxed-prop 'n 'W 'L 's 't)] ['hS (source-prop 'L 't)]
           ['h01 (zero-one-at 'n 's 't)]])
    (function/lam
     [['fu nat] ['hfu (strict-below 'fu 'n)] ['hsf (settled 's (succ 't) 'fu)] ['fk nat] ['fx walk-type]
      ['hf0 (eq-nat (app 'fx nat-zero) nat-zero)] ['hfin (in-range 'n 'fx 'fk)] ['hfk (eq-nat (app 'fx 'fk) 'fu)]]
     (let [p (p-of) t1 (succ 't) len-k (walk-length 'W 'fx 'fk)
           goal (sle (L-at 'L t1 'fu) len-k)]
       (use-disj (settled 's 't 'fu) (eq-nat 'fu p) goal (app (rh :R4) 'fu 'hfu 'hsf)
                 ;; settled before: L(t+1, u) <= L(t, u) <= the walk
                 (function/lam [['hs-fs (settled 's 't 'fu)]]
                               (le-trans (L-at 'L t1 'fu) (L-at 'L 't 'fu) len-k (app (rh :R6) 'fu 'hfu)
                                         (app 'hA 'fu 'hfu 'hs-fs 'fk 'fx 'hf0 'hfin 'hfk)))
                 ;; the chosen node p: the walk's first unsettled node x f bounds it
                 (function/lam
                  [['he-fs (eq-nat 'fu p)]]
                  (let [Q (function/lam [['qs nat]] (conj* (at-most 'qs 'fk) (unsettled 's 't (app 'fx 'qs))))
                        Qat (fn [q] (conj* (at-most q 'fk) (unsettled 's 't (app 'fx q))))
                        decQ (function/lam
                              [['ds nat]]
                              (use-disj (at-most 'ds 'fk) (strict-below 'fk 'ds) (disj* (Qat 'ds) (not* (Qat 'ds)))
                                        (app (function/const* 'nat/at-most-or-strict-below []) 'fk 'ds)
                                        (function/lam
                                         [['hle-d (at-most 'ds 'fk)]]
                                         (use-disj (unsettled 's 't (app 'fx 'ds)) (settled 's 't (app 'fx 'ds)) (disj* (Qat 'ds) (not* (Qat 'ds)))
                                                   (app 'h01 (app 'fx 'ds) (app 'hfin 'ds 'hle-d))
                                                   (function/lam [['hu-d (unsettled 's 't (app 'fx 'ds))]]
                                                                 (app (function/const* 'proposition/left-disjunct []) (Qat 'ds) (not* (Qat 'ds))
                                                                      (conjoin (at-most 'ds 'fk) (unsettled 's 't (app 'fx 'ds)) 'hle-d 'hu-d)))
                                                   (function/lam [['hs-d (settled 's 't (app 'fx 'ds))]]
                                                                 (app (function/const* 'proposition/right-disjunct []) (Qat 'ds) (not* (Qat 'ds))
                                                                      (function/lam [['q-d (Qat 'ds)]]
                                                                                    (both-absurd (s-at 's 't (app 'fx 'ds)) (pright (at-most 'ds 'fk) (unsettled 's 't (app 'fx 'ds)) 'q-d) 'hs-d (falsity)))))))
                                        (function/lam
                                         [['hlt-d (strict-below 'fk 'ds)]]
                                         (app (function/const* 'proposition/right-disjunct []) (Qat 'ds) (not* (Qat 'ds))
                                              (function/lam [['q-d (Qat 'ds)]]
                                                            (app (function/const* 'nat/not-strictly-below-self []) 'fk
                                                                 (amt (succ 'fk) 'ds 'fk 'hlt-d (pleft (at-most 'ds 'fk) (unsettled 's 't (app 'fx 'ds)) 'q-d))))))))
                        ;; x k = u = p is unsettled at t
                        xk-p (app (function/const* 'equality/transitive [type-level]) nat (app 'fx 'fk) 'fu p 'hfk 'he-fs)
                        end-unsettled (subst-nat p (app 'fx 'fk) (nat-sym (app 'fx 'fk) p xk-p) (function/lam [['z-u nat]] (unsettled 's 't 'z-u)) (rh :R2))
                        exists-q (app (function/const* 'proposition/witness [type-level]) nat (function/lam [['w-q nat]] (conj* (at-most 'w-q 'fk) (app Q 'w-q))) 'fk
                                      (conjoin (at-most 'fk 'fk) (app Q 'fk) (at-most-refl 'fk) (conjoin (at-most 'fk 'fk) (unsettled 's 't (app 'fx 'fk)) (at-most-refl 'fk) end-unsettled)))
                        least-body (fn [f] (conj* (at-most f 'fk) (conj* (app Q f) (function/forall [['s2 nat] ['hs2 (strict-below 's2 f)]] (not* (app Q 's2))))))
                        Lp (L-at 'L 't p)
                        goal-p (sle Lp len-k)
                        bound-p
                        (app (app (function/const* 'nat/least-witness []) Q decQ 'fk exists-q) goal-p
                             (function/lam
                              [['ff nat] ['pff (least-body 'ff)]]
                              (let [rest1 (conj* (app Q 'ff) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'ff)]] (not* (app Q 's2))))
                                    f-le (pleft (at-most 'ff 'fk) rest1 'pff)
                                    qf (pleft (app Q 'ff) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'ff)]] (not* (app Q 's2))) (pright (at-most 'ff 'fk) rest1 'pff))
                                    f-least (pright (app Q 'ff) (function/forall [['s2 nat] ['hs2 (strict-below 's2 'ff)]] (not* (app Q 's2))) (pright (at-most 'ff 'fk) rest1 'pff))
                                    xf (app 'fx 'ff)
                                    xf-unsettled (pright (at-most 'ff 'fk) (unsettled 's 't xf) qf)
                                    in-f (function/lam [['tr nat] ['htr (at-most 'tr 'ff)]] (app 'hfin 'tr (amt 'tr 'ff 'fk 'htr f-le)))
                                    pre-settled (function/lam
                                                 [['ps nat] ['hps (strict-below 'ps 'ff)]]
                                                 (let [ps-le (amt 'ps (succ 'ps) 'fk (at-most-succ 'ps) (amt (succ 'ps) 'ff 'fk 'hps f-le))]
                                                   (use-disj (unsettled 's 't (app 'fx 'ps)) (settled 's 't (app 'fx 'ps)) (settled 's 't (app 'fx 'ps))
                                                             (app 'h01 (app 'fx 'ps) (app 'hfin 'ps ps-le))
                                                             (function/lam [['hu-ps (unsettled 's 't (app 'fx 'ps))]]
                                                                           (explode (settled 's 't (app 'fx 'ps))
                                                                                    (app f-least 'ps 'hps (conjoin (at-most 'ps 'fk) (unsettled 's 't (app 'fx 'ps)) ps-le 'hu-ps))))
                                                             (function/lam [['hs-ps (settled 's 't (app 'fx 'ps))]] 'hs-ps))))
                                    walk-f (app (function/const* 'signed/dijkstra-walk-bound []) 'n 'W 'L 's 't 'hC 'hS 'fx 'hf0 'ff in-f pre-settled)   ; L(t, x f) <= len f
                                    argmin (app (rh :R3) xf (app 'hfin 'ff f-le) xf-unsettled)                                                  ; L(t, p) <= L(t, x f)
                                    pw (prefix-le-whole 'n 'W 'fx 'ff 'fk 'hW 'hfin f-le)]
                                (le-trans Lp (L-at 'L 't xf) len-k argmin
                                          (le-trans (L-at 'L 't xf) (walk-length 'W 'fx 'ff) len-k walk-f pw)))))]
                    (subst-nat p 'fu (nat-sym 'fu p 'he-fs) (function/lam [['z-u nat]] (sle (L-at 'L t1 'z-u) len-k))
                               (le-trans (L-at 'L t1 p) Lp len-k (app (rh :R6) p (rh :R1)) bound-p))))))))})

(defn- round-all [n W L s P t]
  (let [props (mapv second (rounds n W L s P t))]
    (reduce (fn [acc prop] (conj* prop acc)) (peek props) (rseq (pop props)))))
(defn- round-parts
  "the eight R proofs out of a round-all proof h"
  [n W L s P t h]
  (let [props (mapv second (rounds n W L s P t))
        nest (fn nest [i] (if (= i (dec (count props))) (props i) (conj* (props i) (nest (inc i)))))]
    (loop [i 0 cur h acc []]
      (if (= i (dec (count props)))
        (conj acc cur)
        (recur (inc i) (pright (props i) (nest (inc i)) cur) (conj acc (pleft (props i) (nest (inc i)) cur)))))))
(defn- inv [n W L s t]
  (conj* (final-prop n W L s t) (conj* (relaxed-prop n W L s t) (conj* (order-prop n L s t) (source-prop L t)))))
(defn- inv-parts [n W L s t h]
  (let [A (final-prop n W L s t) C (relaxed-prop n W L s t) D (order-prop n L s t) S (source-prop L t)]
    {:A (pleft A (conj* C (conj* D S)) h)
     :C (pleft C (conj* D S) (pright A (conj* C (conj* D S)) h))
     :D (pleft D S (pright C (conj* D S) (pright A (conj* C (conj* D S)) h)))
     :S (pright D S (pright C (conj* D S) (pright A (conj* C (conj* D S)) h)))}))
(defn- make-inv [n W L s t a c d sr]
  (let [A (final-prop n W L s t) C (relaxed-prop n W L s t) D (order-prop n L s t) S (source-prop L t)]
    (conjoin A (conj* C (conj* D S)) a (conjoin C (conj* D S) c (conjoin D S d sr)))))

(defn- inv-claim [n W L s P r]
  (function/forall [['hr (function/forall [['t nat] ['ht (strict-below 't r)]] (round-all n W L s P 't))]
                    ['h01 (function/forall [['t nat] ['ht (strict-below 't r)]] (zero-one-at n s 't))]]
                   (inv n W L s r)))

(def invariant-spec
  {:name 'signed/dijkstra-invariant :universes []
   :type (function/forall [['n nat] ['W grid-type] ['L grid-type] ['s grid-type] ['P walk-type] ['hW (nonneg-weights 'n 'W)]
                           ['hbase (function/forall [['bv nat] ['hbv (strict-below 'bv 'n)]] (unsettled 's nat-zero 'bv))]
                           ['hsrc (source-prop 'L nat-zero)] ['r nat]]
                          (inv-claim 'n 'W 'L 's 'P 'r))
   :value
   (function/lam
    [['n nat] ['W grid-type] ['L grid-type] ['s grid-type] ['P walk-type] ['hW (nonneg-weights 'n 'W)]
     ['hbase (function/forall [['bv nat] ['hbv (strict-below 'bv 'n)]] (unsettled 's nat-zero 'bv))]
     ['hsrc (source-prop 'L nat-zero)] ['r nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['rr nat]] (inv-claim 'n 'W 'L 's 'P 'rr))
         ;; r = 0: nothing is settled
         (function/lam
          [['hr (function/forall [['t nat] ['ht (strict-below 't nat-zero)]] (round-all 'n 'W 'L 's 'P 't))]
           ['h01 (function/forall [['t nat] ['ht (strict-below 't nat-zero)]] (zero-one-at 'n 's 't))]]
          (let [none (fn [u hu hsu P] (both-absurd (s-at 's nat-zero u) (app 'hbase u hu) hsu P))]
            (make-inv 'n 'W 'L 's nat-zero
                      (function/lam [['fu nat] ['hfu (strict-below 'fu 'n)] ['hsf (settled 's nat-zero 'fu)] ['fk nat] ['fx walk-type]
                                     ['hf0 (eq-nat (app 'fx nat-zero) nat-zero)] ['hfin (in-range 'n 'fx 'fk)] ['hfk (eq-nat (app 'fx 'fk) 'fu)]]
                                    (none 'fu 'hfu 'hsf (sle (L-at 'L nat-zero 'fu) (walk-length 'W 'fx 'fk))))
                      (function/lam [['u nat] ['hu (strict-below 'u 'n)] ['hsu (settled 's nat-zero 'u)] ['v nat] ['hv (strict-below 'v 'n)]]
                                    (none 'u 'hu 'hsu (sle (L-at 'L nat-zero 'v) (signed-add (L-at 'L nat-zero 'u) (app 'W 'u 'v)))))
                      (function/lam [['ou nat] ['hou (strict-below 'ou 'n)] ['hso (settled 's nat-zero 'ou)] ['ov nat] ['hov (strict-below 'ov 'n)] ['huo (unsettled 's nat-zero 'ov)]]
                                    (none 'ou 'hou 'hso (sle (L-at 'L nat-zero 'ou) (L-at 'L nat-zero 'ov))))
                      'hsrc)))
         (function/lam
          [['r nat] ['ih (inv-claim 'n 'W 'L 's 'P 'r)]
           ['hr (function/forall [['t nat] ['ht (strict-below 't (succ 'r))]] (round-all 'n 'W 'L 's 'P 't))]
           ['h01 (function/forall [['t nat] ['ht (strict-below 't (succ 'r))]] (zero-one-at 'n 's 't))]]
          (let [weak (fn [h] (function/lam [['t nat] ['ht (strict-below 't 'r)]] (app h 't (app (function/const* 'nat/strict-below-weaken []) 't 'r 'ht))))
                prev (app 'ih (weak 'hr) (weak 'h01))
                {:keys [A C D S]} (inv-parts 'n 'W 'L 's 'r prev)
                R (round-parts 'n 'W 'L 's 'P 'r (app 'hr 'r (sb-self 'r)))
                base-args (into ['n 'W 'L 's 'P 'r 'hW] R)
                cite (fn [name & extra] (apply app (function/const* name []) (concat base-args extra)))]
            (make-inv 'n 'W 'L 's (succ 'r)
                      (cite 'signed/dijkstra-final-step A C S (app 'h01 'r (sb-self 'r)))
                      (cite 'signed/dijkstra-relaxed-step C D)
                      (cite 'signed/dijkstra-order-step D)
                      (cite 'signed/dijkstra-source-step S))))
         'r))})

(def theorem-specs [walk-bound-spec stable-spec relaxed-step-spec order-step-spec source-step-spec final-step-spec invariant-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.algorithms.proofs.graph.walk-cycle-cut rainbow.math.nat.extremal-index rainbow.math.sums.value-append])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :dijkstra-invariant theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.algorithms.proofs.graph.dijkstra-invariant))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
