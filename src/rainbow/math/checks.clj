(ns rainbow.math.checks
  "General lemmas: checks. The mathematical facts the corresponding checks rest on,
  each checked by the kernel."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.rational.signed.no-zero-divisors :as no-zero-divisors]
            [rainbow.math.rational.signed.decide-completeness :as decide-completeness]
            [rainbow.math.rational.signed.unit-laws :as unit-laws]
            [rainbow.math.nat.strict-below-split :as split]
            [rainbow.math.nat.strict-below-more :as more]
            [rainbow.math.rational.signed.clamp :as xclamp]
            [rainbow.math.rational.signed.distance :as xdistance]
            [rainbow.math.nat.linear-order :as xlinear]
            [rainbow.math.rational.signed.structural-equality :as xstructural]
            [rainbow.module :as module]))

(def prop-level [:zero])

(def type-level [:succ [:zero]])

(def nat (function/const* 'data/Nat []))

(def nat-zero (function/const* 'data/zero []))

(def bool (function/const* 'data/Bool []))

(def true-value (function/const* 'data/true []))

(def false-value (function/const* 'data/false []))

(def signed (function/const* 'signed/SignedRational []))

(def szero (function/const* 'signed/zero []))

(def sone (function/const* 'signed/one []))

(def environment-type (function/arrow nat signed))

(def trivial (function/const* 'proposition/trivial []))

(defn app [f & args] (apply function/app f args))

(defn succ [n] (app (function/const* 'data/succ []) n))

(defn nadd [a b] (app (function/const* 'algebra/nat-add []) a b))

(defn nmul [a b] (app (function/const* 'nat/multiply []) a b))

(defn decide-at-most [l r] (app (function/const* 'signed/decide-at-most []) l r))

(defn selected-at [at-false at-true choice]
  (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] signed)
       at-false at-true choice))

(defn sle [a b] (app (function/const* 'signed/at-most []) a b))

(defn seqv [a b] (app (function/const* 'signed/equivalent []) a b))

(defn eq-signed [a b] (app (function/const* 'equality/Eq [type-level]) signed a b))

(defn eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))

(defn eq-bool [a b] (app (function/const* 'equality/Eq [type-level]) bool a b))

(defn refl [x] (app (function/const* 'equality/reflexive [type-level]) signed x))

(defn refl-nat [x] (app (function/const* 'equality/reflexive [type-level]) nat x))

(defn refl-bool [x] (app (function/const* 'equality/reflexive [type-level]) bool x))

(defn esym [a b h] (app (function/const* 'equality/symmetric [type-level]) signed a b h))

(defn esym-nat [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))

(defn esym-bool [a b h] (app (function/const* 'equality/symmetric [type-level]) bool a b h))

(defn subst-bool [x y h P px] (app (function/const* 'equality/substitution [type-level]) bool x y h P px))

(defn sb-weaken [i m h] (app (function/const* 'nat/strict-below-weaken []) i m h))

(defn sb-self [m] (app (function/const* 'nat/strict-below-self []) m))

(defn subst [x y h P px] (app (function/const* 'equality/substitution [type-level]) signed x y h P px))

(defn subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))

(defn transitive [a b c ab bc]
  (app (function/const* 'equality/transitive [type-level]) signed a b c ab bc))

(defn at-most [a b] (app (function/const* 'nat/at-most []) a b))

(defn amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))

(defn at-most-succ [a] (app (function/const* 'nat/at-most-successor []) a))

(defn at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))

(defn mul-mono [factor l r h] (app (function/const* 'nat/multiply-right-monotone []) factor l r h))

(defn add-left-mono [prefix l r h] (app (function/const* 'nat/add-left-monotone []) prefix l r h))

(defn add-succ-right [i e] (app (function/const* 'nat/add-successor-right []) i e))

(defn strict-below [i b] (app (function/const* 'nat/strict-below []) i b))

(defn sb-split [i m h] (app (function/const* 'nat/strict-below-successor-split []) i m h))

(defn conjunction [l r] (app (function/const* 'proposition/conjunction []) l r))

(defn conjoin [l r lp rp] (app (function/const* 'proposition/conjoin []) l r lp rp))

(defn use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))

(defn witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))

(defn use-witness [pred result h body]
  (app (function/const* 'proposition/use-witness [type-level]) nat pred result h body))

(defn explode [P h] (app (function/const* 'proposition/explode []) P h))

(def val-type (function/arrow nat signed))

(defn signed-add [a b] (app (function/const* 'signed/add []) a b))

(defn falsity [] (function/const* 'proposition/falsity []))

(defn disjt [l r] (app (function/const* 'proposition/disjunction []) l r))

(defn left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))

(defn right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))

(defn all-at-most-value [A B k] (app (function/const* 'signed/all-at-most-value []) A B k))

(defn expr-sum-value [G k] (app (function/const* 'signed/expr-sum-value []) G k))

(defn both-value [P Q] (selected-at szero Q (decide-at-most sone P)))

(defn all-hold
  "forall i < k, A i <= B i -- what a passing group certifies"
  [A B k] (function/forall [['i nat] ['hi (strict-below 'i k)]] (sle (app A 'i) (app B 'i))))

(defn below-zero-absurd [i hi P]
  (use-witness (function/lam [['e nat]] (eq-nat (nadd (succ i) 'e) nat-zero)) P hi
               (function/lam [['e nat] ['pf (eq-nat (nadd (succ i) 'e) nat-zero)]]
                             (explode P (app (function/const* 'nat/zero-not-successor []) (nadd i 'e) (esym-nat (succ (nadd i 'e)) nat-zero 'pf))))))

(defn zero-is-not-one
  "h : 0 = 1 (signed) -> P"
  [h P]
  (explode P (app (function/const* 'signed/one-not-equivalent-zero [])
                  (subst szero sone h (function/lam [['t signed]] (seqv 't szero)) (app (function/const* 'signed/equivalent-reflexive []) szero)))))

(def all-at-most-value-spec
  {:name 'signed/all-at-most-value :kind :definition :transparency :reducible :universes []
   :type (function/arrow val-type (function/arrow val-type (function/arrow nat signed)))
   :value (function/lam
           [['A val-type] ['B val-type] ['k nat]]
           (app (function/const* 'data/Nat.rec [type-level]) (function/lam [['ignored nat]] signed)
                sone
                (function/lam [['q nat] ['rec signed]] (selected-at szero 'rec (decide-at-most (app 'A 'q) (app 'B 'q))))
                'k))})

(def expr-sum-value-spec
  {:name 'signed/expr-sum-value :kind :definition :transparency :reducible :universes []
   :type (function/arrow val-type (function/arrow nat signed))
   :value (function/lam
           [['G val-type] ['k nat]]
           (app (function/const* 'data/Nat.rec [type-level]) (function/lam [['ignored nat]] signed)
                szero
                (function/lam [['q nat] ['rec signed]] (signed-add 'rec (app 'G 'q)))
                'k))})

(def one-not-at-most-zero-spec
  {:name 'signed/one-not-at-most-zero :universes []
   :type (function/arrow (sle sone szero) (falsity))
   :value (function/lam [['h (sle sone szero)]]
                        (app (function/const* 'signed/one-not-equivalent-zero [])
                             (app (function/const* 'signed/at-most-antisymmetric []) sone szero 'h (function/const* 'signed/zero-at-most-one []))))})

(def all-at-most-sound-spec
  {:name 'signed/all-at-most-sound :universes []
   :type (function/forall [['A val-type] ['B val-type] ['k nat] ['h (eq-signed (all-at-most-value 'A 'B 'k) sone)]] (all-hold 'A 'B 'k))
   :value
   (function/lam
    [['A val-type] ['B val-type] ['k nat]]
    (let [goal (fn [kk] (function/forall [['h (eq-signed (all-at-most-value 'A 'B kk) sone)]] (all-hold 'A 'B kk)))]
      (app (function/const* 'data/Nat.rec [prop-level]) (function/lam [['kk nat]] (goal 'kk))
           (function/lam [['h (eq-signed (all-at-most-value 'A 'B nat-zero) sone)] ['i nat] ['hi (strict-below 'i nat-zero)]]
                         (below-zero-absurd 'i 'hi (sle (app 'A 'i) (app 'B 'i))))
           (function/lam
            [['q nat] ['ih (goal 'q)]]
            (let [aq (app 'A 'q) bq (app 'B 'q) rec (all-at-most-value 'A 'B 'q) dec (decide-at-most aq bq)
                  ;; equality motive: the branch also learns dec = ch
                  ch-goal (fn [ch] (function/forall [['hd (eq-bool dec ch)] ['h (eq-signed (selected-at szero rec ch) sone)]] (all-hold 'A 'B (succ 'q))))]
              (app (function/const* 'data/Bool.rec [prop-level]) (function/lam [['ch bool]] (ch-goal 'ch))
                   (function/lam [['hd (eq-bool dec false-value)] ['h (eq-signed szero sone)] ['i nat] ['hi (strict-below 'i (succ 'q))]]
                                 (zero-is-not-one 'h (sle (app 'A 'i) (app 'B 'i))))
                   (function/lam [['hd (eq-bool dec true-value)] ['h (eq-signed rec sone)] ['i nat] ['hi (strict-below 'i (succ 'q))]]
                                 (use-disj (strict-below 'i 'q) (eq-nat 'i 'q) (sle (app 'A 'i) (app 'B 'i)) (sb-split 'i 'q 'hi)
                                           (function/lam [['hlt (strict-below 'i 'q)]] (app 'ih 'h 'i 'hlt))
                                           (function/lam [['heq (eq-nat 'i 'q)]]
                                                         (subst-nat 'q 'i (esym-nat 'i 'q 'heq) (function/lam [['t nat]] (sle (app 'A 't) (app 'B 't)))
                                                                    (app (function/const* 'signed/decide-at-most-true-sound []) aq bq 'hd)))))
                   dec (refl-bool dec))))
           'k)))})

(def all-at-most-complete-spec
  {:name 'signed/all-at-most-complete :universes []
   :type (function/forall [['A val-type] ['B val-type] ['k nat] ['h (all-hold 'A 'B 'k)]] (eq-signed (all-at-most-value 'A 'B 'k) sone))
   :value
   (function/lam
    [['A val-type] ['B val-type] ['k nat]]
    (let [goal (fn [kk] (function/forall [['h (all-hold 'A 'B kk)]] (eq-signed (all-at-most-value 'A 'B kk) sone)))]
      (app (function/const* 'data/Nat.rec [prop-level]) (function/lam [['kk nat]] (goal 'kk))
           (function/lam [['h (all-hold 'A 'B nat-zero)]] (refl sone))
           (function/lam
            [['q nat] ['ih (goal 'q)] ['h (all-hold 'A 'B (succ 'q))]]
            (let [aq (app 'A 'q) bq (app 'B 'q) rec (all-at-most-value 'A 'B 'q) dec (decide-at-most aq bq)
                  below (function/lam [['i nat] ['hi (strict-below 'i 'q)]] (app 'h 'i (sb-weaken 'i 'q 'hi)))
                  dec-true (app (function/const* 'signed/decide-at-most-true-complete []) aq bq (app 'h 'q (sb-self 'q)))]
              (subst-bool true-value dec (esym-bool dec true-value dec-true) (function/lam [['ch bool]] (eq-signed (selected-at szero rec 'ch) sone)) (app 'ih below))))
           'k)))})

(def all-at-most-zero-or-one-spec
  {:name 'signed/all-at-most-zero-or-one :universes []
   :type (function/forall [['A val-type] ['B val-type] ['k nat]]
                          (disjt (eq-signed (all-at-most-value 'A 'B 'k) szero) (eq-signed (all-at-most-value 'A 'B 'k) sone)))
   :value
   (function/lam
    [['A val-type] ['B val-type] ['k nat]]
    (let [claim (fn [kk] (disjt (eq-signed (all-at-most-value 'A 'B kk) szero) (eq-signed (all-at-most-value 'A 'B kk) sone)))]
      (app (function/const* 'data/Nat.rec [prop-level]) (function/lam [['kk nat]] (claim 'kk))
           (right-disj (eq-signed sone szero) (eq-signed sone sone) (refl sone))
           (function/lam
            [['q nat] ['ih (claim 'q)]]
            (let [rec (all-at-most-value 'A 'B 'q) dec (decide-at-most (app 'A 'q) (app 'B 'q))
                  P (fn [ch] (disjt (eq-signed (selected-at szero rec ch) szero) (eq-signed (selected-at szero rec ch) sone)))]
              (app (function/const* 'data/Bool.rec [prop-level]) (function/lam [['ch bool]] (P 'ch))
                   (left-disj (eq-signed szero szero) (eq-signed szero sone) (refl szero))
                   'ih
                   dec)))
           'k)))})

(def all-at-most-one-of-at-least-one-spec
  {:name 'signed/all-at-most-one-of-at-least-one :universes []
   :type (function/forall [['A val-type] ['B val-type] ['k nat] ['h (sle sone (all-at-most-value 'A 'B 'k))]] (eq-signed (all-at-most-value 'A 'B 'k) sone))
   :value
   (function/lam
    [['A val-type] ['B val-type] ['k nat] ['h (sle sone (all-at-most-value 'A 'B 'k))]]
    (let [v (all-at-most-value 'A 'B 'k)]
      (use-disj (eq-signed v szero) (eq-signed v sone) (eq-signed v sone) (app (function/const* 'signed/all-at-most-zero-or-one []) 'A 'B 'k)
                (function/lam [['h0 (eq-signed v szero)]]
                              (explode (eq-signed v sone) (app (function/const* 'signed/one-not-at-most-zero []) (subst v szero 'h0 (function/lam [['t signed]] (sle sone 't)) 'h))))
                (function/lam [['h1 (eq-signed v sone)]] 'h1))))})

(def both-sound-spec
  {:name 'signed/both-sound :universes []
   :type (function/forall [['P signed] ['Q signed] ['h (eq-signed (both-value 'P 'Q) sone)]] (conjunction (sle sone 'P) (eq-signed 'Q sone)))
   :value
   (function/lam
    [['P signed] ['Q signed]]
    (let [dec (decide-at-most sone 'P) goal (conjunction (sle sone 'P) (eq-signed 'Q sone))]
      (app (app (function/const* 'data/Bool.rec [prop-level])
                (function/lam [['ch bool]] (function/forall [['hd (eq-bool dec 'ch)] ['h (eq-signed (selected-at szero 'Q 'ch) sone)]] goal))
                (function/lam [['hd (eq-bool dec false-value)] ['h (eq-signed szero sone)]] (zero-is-not-one 'h goal))
                (function/lam [['hd (eq-bool dec true-value)] ['h (eq-signed 'Q sone)]]
                              (conjoin (sle sone 'P) (eq-signed 'Q sone) (app (function/const* 'signed/decide-at-most-true-sound []) sone 'P 'hd) 'h))
                dec)
           (refl-bool dec))))})

(def both-complete-spec
  {:name 'signed/both-complete :universes []
   :type (function/forall [['P signed] ['Q signed] ['hp (sle sone 'P)] ['hq (eq-signed 'Q sone)]] (eq-signed (both-value 'P 'Q) sone))
   :value
   (function/lam
    [['P signed] ['Q signed] ['hp (sle sone 'P)] ['hq (eq-signed 'Q sone)]]
    (let [dec (decide-at-most sone 'P) dec-true (app (function/const* 'signed/decide-at-most-true-complete []) sone 'P 'hp)]
      (subst-bool true-value dec (esym-bool dec true-value dec-true) (function/lam [['ch bool]] (eq-signed (selected-at szero 'Q 'ch) sone)) 'hq)))})

(def all-at-most-value-congruence-spec
  {:name 'signed/all-at-most-value-congruence :universes []
   :type (function/forall [['A val-type] ['B val-type] ['A2 val-type] ['B2 val-type]
                           ['HA (function/forall [['i nat]] (eq-signed (app 'A 'i) (app 'A2 'i)))] ['HB (function/forall [['i nat]] (eq-signed (app 'B 'i) (app 'B2 'i)))] ['k nat]]
                          (eq-signed (all-at-most-value 'A 'B 'k) (all-at-most-value 'A2 'B2 'k)))
   :value
   (function/lam
    [['A val-type] ['B val-type] ['A2 val-type] ['B2 val-type]
     ['HA (function/forall [['i nat]] (eq-signed (app 'A 'i) (app 'A2 'i)))] ['HB (function/forall [['i nat]] (eq-signed (app 'B 'i) (app 'B2 'i)))] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level]) (function/lam [['kk nat]] (eq-signed (all-at-most-value 'A 'B 'kk) (all-at-most-value 'A2 'B2 'kk)))
         (refl sone)
         (function/lam
          [['q nat] ['ih (eq-signed (all-at-most-value 'A 'B 'q) (all-at-most-value 'A2 'B2 'q))]]
          (let [rec (all-at-most-value 'A 'B 'q) aq (app 'A 'q) bq (app 'B 'q) lhs (selected-at szero rec (decide-at-most aq bq))
                s1 (subst aq (app 'A2 'q) (app 'HA 'q) (function/lam [['t signed]] (eq-signed lhs (selected-at szero rec (decide-at-most 't bq)))) (refl lhs))
                s2 (subst bq (app 'B2 'q) (app 'HB 'q) (function/lam [['t signed]] (eq-signed lhs (selected-at szero rec (decide-at-most (app 'A2 'q) 't)))) s1)]
            (subst rec (all-at-most-value 'A2 'B2 'q) 'ih (function/lam [['t signed]] (eq-signed lhs (selected-at szero 't (decide-at-most (app 'A2 'q) (app 'B2 'q))))) s2)))
         'k))})

(def expr-sum-value-congruence-spec
  {:name 'signed/expr-sum-value-congruence :universes []
   :type (function/forall [['G val-type] ['G2 val-type] ['H (function/forall [['i nat]] (eq-signed (app 'G 'i) (app 'G2 'i)))] ['k nat]]
                          (eq-signed (expr-sum-value 'G 'k) (expr-sum-value 'G2 'k)))
   :value
   (function/lam
    [['G val-type] ['G2 val-type] ['H (function/forall [['i nat]] (eq-signed (app 'G 'i) (app 'G2 'i)))] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level]) (function/lam [['kk nat]] (eq-signed (expr-sum-value 'G 'kk) (expr-sum-value 'G2 'kk)))
         (refl szero)
         (function/lam
          [['q nat] ['ih (eq-signed (expr-sum-value 'G 'q) (expr-sum-value 'G2 'q))]]
          (let [rec (expr-sum-value 'G 'q) gq (app 'G 'q) lhs (signed-add rec gq)
                s1 (subst gq (app 'G2 'q) (app 'H 'q) (function/lam [['t signed]] (eq-signed lhs (signed-add rec 't))) (refl lhs))]
            (subst rec (expr-sum-value 'G2 'q) 'ih (function/lam [['t signed]] (eq-signed lhs (signed-add 't (app 'G2 'q)))) s1)))
         'k))})

(defn sum-agree-below [k]
  (function/forall [['a nat] ['ha (strict-below 'a k)]] (eq-signed (app 'G 'a) (app 'G2 'a))))

(def expr-sum-value-congruence-below-spec
  {:name 'signed/expr-sum-value-congruence-below :universes []
   :type (function/forall [['G val-type] ['G2 val-type] ['k nat] ['H (sum-agree-below 'k)]]
                          (eq-signed (expr-sum-value 'G 'k) (expr-sum-value 'G2 'k)))
   :value
   (function/lam
    [['G val-type] ['G2 val-type] ['k nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['j nat]] (function/forall [['H (sum-agree-below 'j)]] (eq-signed (expr-sum-value 'G 'j) (expr-sum-value 'G2 'j))))
         (function/lam [['H (sum-agree-below nat-zero)]] (refl szero))
         (function/lam
          [['q nat] ['ih (function/forall [['H (sum-agree-below 'q)]] (eq-signed (expr-sum-value 'G 'q) (expr-sum-value 'G2 'q)))]
           ['H (sum-agree-below (succ 'q))]]
          (let [rec (expr-sum-value 'G 'q) gq (app 'G 'q) lhs (signed-add rec gq)
                below-q (function/lam [['a nat] ['ha (strict-below 'a 'q)]] (app 'H 'a (sb-weaken 'a 'q 'ha)))
                s1 (subst gq (app 'G2 'q) (app 'H 'q (sb-self 'q)) (function/lam [['t signed]] (eq-signed lhs (signed-add rec 't))) (refl lhs))]
            (subst rec (expr-sum-value 'G2 'q) (app 'ih below-q) (function/lam [['t signed]] (eq-signed lhs (signed-add 't (app 'G2 'q)))) s1)))
         'k))})

(def theorem-specs [all-at-most-value-spec expr-sum-value-spec one-not-at-most-zero-spec all-at-most-sound-spec all-at-most-complete-spec all-at-most-zero-or-one-spec all-at-most-one-of-at-least-one-spec both-sound-spec both-complete-spec all-at-most-value-congruence-spec expr-sum-value-congruence-spec expr-sum-value-congruence-below-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.infinite rainbow.math.rational.nnrat.identities rainbow.math.nat.at-most-cancellation rainbow.math.rational.nnrat.order-equivalence rainbow.math.rational.nnrat.archimedean rainbow.math.rational.nnrat.add-monotone rainbow.math.rational.nnrat.add-cancellation rainbow.math.rational.nnrat.additive-reassociation rainbow.math.rational.signed.order-transitivity rainbow.math.rational.signed.convergence rainbow.math.rational.signed.order-respects rainbow.math.rational.signed.limit-uniqueness rainbow.math.rational.signed.strict-order rainbow.math.rational.signed.multiply rainbow.math.rational.nnrat.multiply-commute rainbow.math.rational.nnrat.product-reassociation rainbow.math.rational.nnrat.distribute-right rainbow.math.rational.nnrat.ring rainbow.math.rational.nnrat.multiply-monotone rainbow.math.rational.nnrat.order-difference rainbow.math.rational.signed.multiply-order rainbow.math.rational.signed.equivalence-laws rainbow.math.rational.nnrat.minmax rainbow.math.rational.nnrat.farkas-elim-list rainbow.math.rational.signed.no-zero-divisors rainbow.math.rational.signed.decide-order rainbow.math.rational.signed.decide-reflexive rainbow.math.logic.boolean-and rainbow.math.rational.signed.decide-equivalence rainbow.math.rational.signed.decide-completeness rainbow.math.rational.signed.unit-laws rainbow.math.nat.strict-below-split rainbow.math.nat.strict-below-more rainbow.math.rational.signed.clamp rainbow.math.rational.signed.distance rainbow.math.nat.linear-order rainbow.math.rational.signed.structural-equality])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :clojure-checker-combinators theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.checks))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
