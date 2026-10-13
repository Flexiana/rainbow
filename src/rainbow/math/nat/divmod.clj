(ns rainbow.math.nat.divmod
  "Row/column of a FLAT PAIR INDEX, kernel-side, with the bounds the pair-vector families need
  (Floyd-Warshall's round is a block of n*n components indexed by c = col + row*n).
     nat/at-most-split : a <= b -> a = b \\/ a < b            (case on the witness)
     nat/at-most-or-strict-below : b <= a \\/ a < b          (totality, through nat/decide-at-most)
     nat/col-of n c, nat/row-of n c -- a carry recursion on c: the column steps by one and wraps to
        zero (row steps) when the decided test `succ (succ col) <= n` fails
     nat/col-of-below : 0 < n -> col-of n c < n
     nat/col-row-decomposition : 0 < n -> c = col-of n c + (row-of n c) * n
     nat/row-of-below : 0 < n -> c < n*n -> row-of n c < n     (from the decomposition by
        contradiction: n <= row would put row*n >= n*n above c)
     nat/pair-index-below : a < n -> b < n -> a + b*n < n*n
  The wrap test decides `succ (succ col) <= n` rather than `succ col = n` so that its true branch
  gives the strict bound directly (decide-at-most-true-sound) and its false branch, together with
  col < n and at-most-split, forces succ col = n."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.strict-below-more :as more]
            [rainbow.math.nat.at-most-add :as at-most-add]
            [rainbow.math.rational.nnrat.harmonic-convergence :as harmonic]
            [rainbow.math.rational.signed.decide-completeness :as decide-completeness]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(def ^:private bool (function/const* 'data/Bool []))
(def ^:private true-value (function/const* 'data/true []))
(def ^:private false-value (function/const* 'data/false []))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- ndecide [a b] (app (function/const* 'nat/decide-at-most []) a b))
(defn- selected-nat [at-false at-true choice]
  (app (function/const* 'data/Bool.rec [type-level]) (function/lam [['ignored bool]] nat) at-false at-true choice))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- eq-bool [a b] (app (function/const* 'equality/Eq [type-level]) bool a b))
(defn- refl-nat [x] (app (function/const* 'equality/reflexive [type-level]) nat x))
(defn- refl-bool [x] (app (function/const* 'equality/reflexive [type-level]) bool x))
(defn- esym-nat [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- etr-nat [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- at-most-refl [a] (app (function/const* 'nat/at-most-reflexive []) a))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- add-zero-right [x] (app (function/const* 'algebra/nat-add-zero-right []) x))
(defn- add-succ-right [i e] (app (function/const* 'nat/add-successor-right []) i e))
(defn- succ-mono [k n h] (app (function/const* 'nat/successor-monotone []) k n h))
(defn- mul-mono [factor l r h] (app (function/const* 'nat/multiply-right-monotone []) factor l r h))
(defn- add-right-mono [suffix l r h] (app (function/const* 'nat/add-right-monotone []) suffix l r h))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- witness [P w pf] (app (function/const* 'proposition/witness [type-level]) nat P w pf))
(defn- use-witness [pred result h body] (app (function/const* 'proposition/use-witness [type-level]) nat pred result h body))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- col-of [n c] (app (function/const* 'nat/col-of []) n c))
(defn- row-of [n c] (app (function/const* 'nat/row-of []) n c))

(def at-most-split-spec
  {:name 'nat/at-most-split :universes []
   :type (function/forall [['a nat] ['b nat] ['h (at-most 'a 'b)]] (disjt (eq-nat 'a 'b) (strict-below 'a 'b)))
   :value
   (function/lam
    [['a nat] ['b nat] ['h (at-most 'a 'b)]]
    (use-witness (function/lam [['e nat]] (eq-nat (nadd 'a 'e) 'b)) (disjt (eq-nat 'a 'b) (strict-below 'a 'b)) 'h
                 (function/lam
                  [['e nat]]
                  (app (function/const* 'data/Nat.rec [prop-level])
                       (function/lam [['ee nat]] (function/forall [['pf (eq-nat (nadd 'a 'ee) 'b)]] (disjt (eq-nat 'a 'b) (strict-below 'a 'b))))
                       (function/lam [['pf (eq-nat (nadd 'a nat-zero) 'b)]]
                                     (left-disj (eq-nat 'a 'b) (strict-below 'a 'b)
                                                (etr-nat 'a (nadd 'a nat-zero) 'b (esym-nat (nadd 'a nat-zero) 'a (add-zero-right 'a)) 'pf)))
                       (function/lam
                        [['ep nat] ['ignored (function/forall [['pf (eq-nat (nadd 'a 'ep) 'b)]] (disjt (eq-nat 'a 'b) (strict-below 'a 'b)))]
                         ['pf (eq-nat (nadd 'a (succ 'ep)) 'b)]]
                        (right-disj (eq-nat 'a 'b) (strict-below 'a 'b)
                                    (witness (function/lam [['e2 nat]] (eq-nat (nadd (succ 'a) 'e2) 'b)) 'ep
                                             (etr-nat (nadd (succ 'a) 'ep) (nadd 'a (succ 'ep)) 'b
                                                      (esym-nat (nadd 'a (succ 'ep)) (succ (nadd 'a 'ep)) (add-succ-right 'a 'ep)) 'pf))))
                       'e))))})

(def at-most-or-strict-below-spec
  {:name 'nat/at-most-or-strict-below :universes []
   :type (function/forall [['a nat] ['b nat]] (disjt (at-most 'b 'a) (strict-below 'a 'b)))
   :value
   (function/lam
    [['a nat] ['b nat]]
    (let [dec (ndecide 'b 'a) goal (disjt (at-most 'b 'a) (strict-below 'a 'b))]
      (app (function/const* 'data/Bool.rec [prop-level])
           (function/lam [['ch bool]] (function/forall [['hd (eq-bool dec 'ch)]] goal))
           (function/lam [['hd (eq-bool dec false-value)]]
                         (use-disj (eq-nat 'a 'b) (strict-below 'a 'b) goal
                                   (app (function/const* 'nat/at-most-split []) 'a 'b (app (function/const* 'nat/decide-at-most-false-reverse []) 'b 'a 'hd))
                                   (function/lam [['heq (eq-nat 'a 'b)]]
                                                 (left-disj (at-most 'b 'a) (strict-below 'a 'b)
                                                            (subst-nat 'a 'b 'heq (function/lam [['t nat]] (at-most 't 'a)) (at-most-refl 'a))))
                                   (function/lam [['hlt (strict-below 'a 'b)]] (right-disj (at-most 'b 'a) (strict-below 'a 'b) 'hlt))))
           (function/lam [['hd (eq-bool dec true-value)]]
                         (left-disj (at-most 'b 'a) (strict-below 'a 'b) (app (function/const* 'nat/decide-at-most-true-sound []) 'b 'a 'hd)))
           dec (refl-bool dec))))})

(def col-of-spec
  {:name 'nat/col-of :kind :definition :transparency :reducible :universes []
   :type (function/arrow nat (function/arrow nat nat))
   :value (function/lam
           [['n nat] ['c nat]]
           (app (function/const* 'data/Nat.rec [type-level])
                (function/lam [['ignored nat]] nat)
                nat-zero
                (function/lam [['cp nat] ['col nat]] (selected-nat nat-zero (succ 'col) (ndecide (succ (succ 'col)) 'n)))
                'c))})

(def row-of-spec
  {:name 'nat/row-of :kind :definition :transparency :reducible :universes []
   :type (function/arrow nat (function/arrow nat nat))
   :value (function/lam
           [['n nat] ['c nat]]
           (app (function/const* 'data/Nat.rec [type-level])
                (function/lam [['ignored nat]] nat)
                nat-zero
                (function/lam [['cp nat] ['row nat]] (selected-nat (succ 'row) 'row (ndecide (succ (succ (col-of 'n 'cp))) 'n)))
                'c))})

(def col-of-below-spec
  {:name 'nat/col-of-below :universes []
   :type (function/forall [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat]] (strict-below (col-of 'n 'c) 'n))
   :value
   (function/lam
    [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['cc nat]] (strict-below (col-of 'n 'cc) 'n))
         'hn
         (function/lam
          [['cp nat] ['ih (strict-below (col-of 'n 'cp) 'n)]]
          (let [col (col-of 'n 'cp) dec (ndecide (succ (succ col)) 'n)]
            (app (function/const* 'data/Bool.rec [prop-level])
                 (function/lam [['ch bool]] (function/forall [['hd (eq-bool dec 'ch)]] (strict-below (selected-nat nat-zero (succ col) 'ch) 'n)))
                 (function/lam [['hd (eq-bool dec false-value)]] 'hn)
                 (function/lam [['hd (eq-bool dec true-value)]] (app (function/const* 'nat/decide-at-most-true-sound []) (succ (succ col)) 'n 'hd))
                 dec (refl-bool dec))))
         'c))})

(def col-row-decomposition-spec
  {:name 'nat/col-row-decomposition :universes []
   :type (function/forall [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat]] (eq-nat 'c (nadd (col-of 'n 'c) (nmul (row-of 'n 'c) 'n))))
   :value
   (function/lam
    [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat]]
    (app (function/const* 'data/Nat.rec [prop-level])
         (function/lam [['cc nat]] (eq-nat 'cc (nadd (col-of 'n 'cc) (nmul (row-of 'n 'cc) 'n))))
         (refl-nat nat-zero)
         (function/lam
          [['cp nat] ['ih (eq-nat 'cp (nadd (col-of 'n 'cp) (nmul (row-of 'n 'cp) 'n)))]]
          (let [col (col-of 'n 'cp) row (row-of 'n 'cp) dec (ndecide (succ (succ col)) 'n)
                goal (fn [ch] (eq-nat (succ 'cp) (nadd (selected-nat nat-zero (succ col) ch) (nmul (selected-nat (succ row) row ch) 'n))))
                ;; succ cp = succ (col + row*n) = succ col + row*n
                step (subst-nat 'cp (nadd col (nmul row 'n)) 'ih (function/lam [['t nat]] (eq-nat (succ 'cp) (succ 't))) (refl-nat (succ 'cp)))]
            (app (function/const* 'data/Bool.rec [prop-level])
                 (function/lam [['ch bool]] (function/forall [['hd (eq-bool dec 'ch)]] (goal 'ch)))
                 ;; wrap: succ col = n, so succ cp = n + row*n = (succ row)*n
                 (function/lam
                  [['hd (eq-bool dec false-value)]]
                  (let [col-lt (app (function/const* 'nat/col-of-below []) 'n 'hn 'cp)
                        not-strict (app (function/const* 'nat/decide-at-most-false-sound []) (succ (succ col)) 'n 'hd)
                        sc-eq-n (use-disj (eq-nat (succ col) 'n) (strict-below (succ col) 'n) (eq-nat (succ col) 'n)
                                          (app (function/const* 'nat/at-most-split []) (succ col) 'n col-lt)
                                          (function/lam [['he (eq-nat (succ col) 'n)]] 'he)
                                          (function/lam [['hl (strict-below (succ col) 'n)]] (explode (eq-nat (succ col) 'n) (app not-strict 'hl))))]
                    (subst-nat (succ col) 'n sc-eq-n (function/lam [['t nat]] (eq-nat (succ 'cp) (nadd 't (nmul row 'n)))) step)))
                 (function/lam [['hd (eq-bool dec true-value)]] step)
                 dec (refl-bool dec))))
         'c))})

(def row-of-below-spec
  {:name 'nat/row-of-below :universes []
   :type (function/forall [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat] ['hc (strict-below 'c (nmul 'n 'n))]] (strict-below (row-of 'n 'c) 'n))
   :value
   (function/lam
    [['n nat] ['hn (strict-below nat-zero 'n)] ['c nat] ['hc (strict-below 'c (nmul 'n 'n))]]
    (let [row (row-of 'n 'c) col (col-of 'n 'c) nn (nmul 'n 'n)]
      (use-disj (at-most 'n row) (strict-below row 'n) (strict-below row 'n)
                (app (function/const* 'nat/at-most-or-strict-below []) row 'n)
                (function/lam
                 [['hle (at-most 'n row)]]
                 (let [nn-le-rown (mul-mono 'n 'n row 'hle)
                       rown-le-c (subst-nat (nadd col (nmul row 'n)) 'c (esym-nat 'c (nadd col (nmul row 'n)) (app (function/const* 'nat/col-row-decomposition []) 'n 'hn 'c))
                                            (function/lam [['t nat]] (at-most (nmul row 'n) 't)) (app (function/const* 'nat/at-most-add-left []) (nmul row 'n) col))
                       nn-le-c (amt nn (nmul row 'n) 'c nn-le-rown rown-le-c)
                       absurd (amt (succ nn) (succ 'c) nn (succ-mono nn 'c nn-le-c) 'hc)]
                   (explode (strict-below row 'n) (app (function/const* 'nat/not-strictly-below-self []) nn absurd))))
                (function/lam [['hlt (strict-below row 'n)]] 'hlt))))})

(def pair-index-below-spec
  {:name 'nat/pair-index-below :universes []
   :type (function/forall [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)] ['hb (strict-below 'b 'n)]] (strict-below (nadd 'a (nmul 'b 'n)) (nmul 'n 'n)))
   :value (function/lam
           [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)] ['hb (strict-below 'b 'n)]]
           (amt (nadd (succ 'a) (nmul 'b 'n)) (nmul (succ 'b) 'n) (nmul 'n 'n)
                (add-right-mono (nmul 'b 'n) (succ 'a) 'n 'ha)
                (mul-mono 'n (succ 'b) 'n 'hb)))})

(def theorem-specs [at-most-split-spec at-most-or-strict-below-spec col-of-spec row-of-spec
                    col-of-below-spec col-row-decomposition-spec row-of-below-spec pair-index-below-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.strict-below-more rainbow.math.nat.at-most-add rainbow.math.rational.nnrat.harmonic-convergence rainbow.math.rational.signed.decide-completeness])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-divmod theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.divmod))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
