(ns rainbow.math.nat.pair-index-inverse
  "INVERTING THE PAIR INDEX. The families store a matrix entry (u, v) at slot v + u*n and read a slot
  c back as (row-of n c, col-of n c). nat_divmod proves c = col-of n c + row-of n c * n with
  col-of n c < n. This module proves the converse, that the decomposition is unique, so a slot
  names its entry:

     nat/pair-index-unique-row : a < n -> a' < n -> a + b*n = a' + b'*n -> b = b'
     nat/pair-index-unique-col : a < n -> a' < n -> a + b*n = a' + b'*n -> a = a'
     nat/row-of-pair-index     : a < n -> row-of n (a + b*n) = b
     nat/col-of-pair-index     : a < n -> col-of n (a + b*n) = a

  Uniqueness is by trichotomy on b, b': if b < b' then a + b*n < (b+1)*n <= b'*n <= a' + b'*n, which
  contradicts the equation; symmetrically for b' < b. Then a = a' by cancellation."
  (:require [rainbow.module :as module]
            [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.divmod :as divmod]))

(def ^:private prop-level [:zero])
(def ^:private type-level [:succ [:zero]])
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- app [f & args] (apply function/app f args))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(defn- nadd [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- eq-nat [a b] (app (function/const* 'equality/Eq [type-level]) nat a b))
(defn- esym [a b h] (app (function/const* 'equality/symmetric [type-level]) nat a b h))
(defn- etrans [a b c h1 h2] (app (function/const* 'equality/transitive [type-level]) nat a b c h1 h2))
(defn- subst-nat [x y h P px] (app (function/const* 'equality/substitution [type-level]) nat x y h P px))
(defn- at-most [a b] (app (function/const* 'nat/at-most []) a b))
(defn- strict-below [i b] (app (function/const* 'nat/strict-below []) i b))
(defn- amt [a m z h1 h2] (app (function/const* 'nat/at-most-transitive []) a m z h1 h2))
(defn- mul-mono [factor l r h] (app (function/const* 'nat/multiply-right-monotone []) factor l r h))
(defn- add-right-mono [suffix l r h] (app (function/const* 'nat/add-right-monotone []) suffix l r h))
(defn- add-comm [l r] (app (function/const* 'nat/add-commutative []) l r))
(defn- add-left-cancel [p l r h] (app (function/const* 'nat/add-left-cancel []) p l r h))
(defn- disjunction [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- use-disj [l r res either onl onr] (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))
(defn- explode [P h] (app (function/const* 'proposition/explode []) P h))
(defn- falsity [] (function/const* 'proposition/falsity []))

(defn- equation [a b a2 b2 n] (eq-nat (nadd a (nmul b n)) (nadd a2 (nmul b2 n))))

(defn- below-contradiction
  "a < n, a + b*n = a2 + b2*n, b < b2 |- False:
   succ (a + b*n) = (succ a) + b*n <= n + b*n = (succ b)*n <= b2*n <= a2 + b2*n = a + b*n."
  [n a b a2 b2 ha h hlt]
  (let [X (nadd a (nmul b n))
        s1 (add-right-mono (nmul b n) (succ a) n ha)                      ; succ a + b n <= n + b n = (succ b) n
        s2 (mul-mono n (succ b) b2 hlt)                                  ; (succ b) n <= b2 n
        s3 (app (function/const* 'nat/at-most-add-left []) (nmul b2 n) a2) ; b2 n <= a2 + b2 n
        up (amt (succ X) (nmul b2 n) (nadd a2 (nmul b2 n)) (amt (succ X) (nmul (succ b) n) (nmul b2 n) s1 s2) s3)
        self (subst-nat (nadd a2 (nmul b2 n)) X (esym X (nadd a2 (nmul b2 n)) h)
                        (function/lam [['t nat]] (at-most (succ X) 't)) up)]
    (app (function/const* 'nat/not-strictly-below-self []) X self)))

(def unique-row-spec
  {:name 'nat/pair-index-unique-row :universes []
   :type (function/forall [['n nat] ['a nat] ['b nat] ['a2 nat] ['b2 nat]
                           ['ha (strict-below 'a 'n)] ['ha2 (strict-below 'a2 'n)] ['h (equation 'a 'b 'a2 'b2 'n)]]
                          (eq-nat 'b 'b2))
   :value (function/lam
           [['n nat] ['a nat] ['b nat] ['a2 nat] ['b2 nat]
            ['ha (strict-below 'a 'n)] ['ha2 (strict-below 'a2 'n)] ['h (equation 'a 'b 'a2 'b2 'n)]]
           (let [goal (eq-nat 'b 'b2)
                 h-back (esym (nadd 'a (nmul 'b 'n)) (nadd 'a2 (nmul 'b2 'n)) 'h)]
             (use-disj (at-most 'b2 'b) (strict-below 'b 'b2) goal
                       (app (function/const* 'nat/at-most-or-strict-below []) 'b 'b2)
                       (function/lam
                        [['hle (at-most 'b2 'b)]]
                        (use-disj (eq-nat 'b2 'b) (strict-below 'b2 'b) goal
                                  (app (function/const* 'nat/at-most-split []) 'b2 'b 'hle)
                                  (function/lam [['he (eq-nat 'b2 'b)]] (esym 'b2 'b 'he))
                                  (function/lam [['hlt (strict-below 'b2 'b)]]
                                                (explode goal (below-contradiction 'n 'a2 'b2 'a 'b 'ha2 h-back 'hlt)))))
                       (function/lam [['hlt (strict-below 'b 'b2)]]
                                     (explode goal (below-contradiction 'n 'a 'b 'a2 'b2 'ha 'h 'hlt))))))})

(def unique-col-spec
  {:name 'nat/pair-index-unique-col :universes []
   :type (function/forall [['n nat] ['a nat] ['b nat] ['a2 nat] ['b2 nat]
                           ['ha (strict-below 'a 'n)] ['ha2 (strict-below 'a2 'n)] ['h (equation 'a 'b 'a2 'b2 'n)]]
                          (eq-nat 'a 'a2))
   :value (function/lam
           [['n nat] ['a nat] ['b nat] ['a2 nat] ['b2 nat]
            ['ha (strict-below 'a 'n)] ['ha2 (strict-below 'a2 'n)] ['h (equation 'a 'b 'a2 'b2 'n)]]
           (let [same-b (app (function/const* 'nat/pair-index-unique-row []) 'n 'a 'b 'a2 'b2 'ha 'ha2 'h)
                 bn (nmul 'b 'n)
                 ;; a + b n = a2 + b n
                 h1 (subst-nat 'b2 'b (esym 'b 'b2 same-b)
                               (function/lam [['t nat]] (eq-nat (nadd 'a bn) (nadd 'a2 (nmul 't 'n)))) 'h)
                 ;; b n + a = b n + a2
                 h2 (etrans (nadd bn 'a) (nadd 'a bn) (nadd bn 'a2)
                            (add-comm bn 'a)
                            (etrans (nadd 'a bn) (nadd 'a2 bn) (nadd bn 'a2) h1 (add-comm 'a2 bn)))]
             (add-left-cancel bn 'a 'a2 h2)))})

(defn- positive-of-below
  "a < n |- 0 < n: the witness of a < n shifted by a (succ 0 + (a + e) and succ a + e both reduce to succ (a + e))."
  [a n ha]
  (app ha (strict-below nat-zero n)
       (function/lam [['e nat] ['pf (eq-nat (nadd (succ a) 'e) n)]]
                     (app (function/const* 'proposition/witness [type-level]) nat
                          (function/lam [['x nat]] (eq-nat (nadd (succ nat-zero) 'x) n))
                          (nadd a 'e) 'pf))))

(defn- decomposition-equation
  "for c = a + b n: col c + row c * n = a + b n, from nat/col-row-decomposition"
  [n a b hn]
  (let [c (nadd a (nmul b n))]
    (esym c (nadd (app (function/const* 'nat/col-of []) n c) (nmul (app (function/const* 'nat/row-of []) n c) n))
          (app (function/const* 'nat/col-row-decomposition []) n hn c))))

(def row-of-pair-spec
  {:name 'nat/row-of-pair-index :universes []
   :type (function/forall [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)]]
                          (eq-nat (app (function/const* 'nat/row-of []) 'n (nadd 'a (nmul 'b 'n))) 'b))
   :value (function/lam
           [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)]]
           (let [hn (positive-of-below 'a 'n 'ha) c (nadd 'a (nmul 'b 'n))
                 col (app (function/const* 'nat/col-of []) 'n c) row (app (function/const* 'nat/row-of []) 'n c)]
             (app (function/const* 'nat/pair-index-unique-row []) 'n col row 'a 'b
                  (app (function/const* 'nat/col-of-below []) 'n hn c) 'ha
                  (decomposition-equation 'n 'a 'b hn))))})

(def col-of-pair-spec
  {:name 'nat/col-of-pair-index :universes []
   :type (function/forall [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)]]
                          (eq-nat (app (function/const* 'nat/col-of []) 'n (nadd 'a (nmul 'b 'n))) 'a))
   :value (function/lam
           [['n nat] ['a nat] ['b nat] ['ha (strict-below 'a 'n)]]
           (let [hn (positive-of-below 'a 'n 'ha) c (nadd 'a (nmul 'b 'n))
                 col (app (function/const* 'nat/col-of []) 'n c) row (app (function/const* 'nat/row-of []) 'n c)]
             (app (function/const* 'nat/pair-index-unique-col []) 'n col row 'a 'b
                  (app (function/const* 'nat/col-of-below []) 'n hn c) 'ha
                  (decomposition-equation 'n 'a 'b hn))))})

(def theorem-specs [unique-row-spec unique-col-spec row-of-pair-spec col-of-pair-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.divmod])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nat-pair-index-inverse theorem-specs)))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.nat.pair-index-inverse))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
