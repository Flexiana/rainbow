(ns rainbow.math.rational.nnrat.add-zero-split
  "Nonnegativity forces zero: for nonnegative rationals, a sum equivalent to 0
  forces each summand to 0.

    nnrat/add-zero-split-left  : (a + b) ~ 0 -> a ~ 0
    nnrat/add-zero-split-right : (a + b) ~ 0 -> b ~ 0

  This is the crux behind complementary slackness / KKT optimality conditions:
  a zero duality gap b.y - c.x = sum of nonnegative slack terms ~ 0 forces every
  slack term to 0.  Because nnrat carries no negatives, cancellation cannot hide a
  positive term.

  Proof: (a+b) ~ 0 unfolds to the cross product (na*db + nb*da) * 1 = 0 * den, so
  the nat numerator na*db + nb*da = 0; nat/sum-zero-left/right split it to
  na*db = 0 and nb*da = 0; and since db, da are positive (succ _), the new nat
  lemma multiply-succ-zero-left gives na = 0 and nb = 0, i.e. a ~ 0 and b ~ 0.
  Native and axiom-free; chains nnrat-nat-at-most-cancellation (for nat/sum-zero-left)
  on d63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.module :as module]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.at-most-cancellation :as cancel]))

(def type-level [:succ [:zero]])
(def nat (function/const* 'data/Nat []))
(def nnrat (function/const* 'nnrat/NonnegativeRational []))
(def zero-nat (function/const* 'data/zero []))
(defn- succ [v] (function/app (function/const* 'data/succ []) v))

(defn- numerator [v] (function/app (function/const* 'nnrat/numerator []) v))
(defn- denominator [v] (function/app (function/const* 'nnrat/denominator []) v))
(defn- dpre [v] (function/app (function/const* 'nnrat/denominator-predecessor []) v))
(defn- nadd [a b] (function/app (function/const* 'algebra/nat-add []) a b))
(defn- nmul [a b] (function/app (function/const* 'nat/multiply []) a b))
(defn- eq-nat [a b] (function/equality type-level nat a b))
(defn- radd [a b] (function/app (function/const* 'nnrat/add []) a b))
(defn- equiv [a b] (function/app (function/const* 'nnrat/equivalent []) a b))
(def nnrat-zero (function/const* 'nnrat/zero []))
(defn- transitive [l m r p q]
  (function/app (function/const* 'equality/transitive [type-level]) nat l m r p q))
(defn- symmetric [l r p]
  (function/app (function/const* 'equality/symmetric [type-level]) nat l r p))
(defn- reflexive-nat [v]
  (function/app (function/const* 'equality/reflexive [type-level]) nat v))
(defn- mult-one-right [v] (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- zero-not-successor [v] (function/app (function/const* 'nat/zero-not-successor []) v))
(defn- explode [goal falsity] (function/app (function/const* 'proposition/explode []) goal falsity))
(defn- nat-rec [motive base step n]
  (function/app (function/const* 'data/Nat.rec [[:zero]]) motive base step n))
(defn- sum-zero-left [x y h] (function/app (function/const* 'nat/sum-zero-left []) x y h))
(defn- sum-zero-right [x y h] (function/app (function/const* 'nat/sum-zero-right []) x y h))
(defn- multiply-succ-zero-left [na m h]
  (function/app (function/const* 'nat/multiply-succ-zero-left []) na m h))

;; ---- nat/sum-zero-right : (x + y = 0) -> (y = 0) ----------------------------
;; nat-add recurses on the LEFT: 0+y=y reduces (base returns h); (succ k)+y=succ(k+y).
(def sum-zero-right-spec
  {:name 'nat/sum-zero-right :universes []
   :type (function/forall [['x nat] ['y nat] ['h (eq-nat (nadd 'x 'y) zero-nat)]]
                          (eq-nat 'y zero-nat))
   :value
   (function/lam
    [['x nat] ['y nat]]
    (nat-rec
     (function/lam [['xv nat]]
                   (function/arrow (eq-nat (nadd 'xv 'y) zero-nat) (eq-nat 'y zero-nat)))
     ;; base x=0 : (0+y=0) -> (y=0) ; 0+y reduces to y
     (function/lam [['h0 (eq-nat (nadd zero-nat 'y) zero-nat)]] 'h0)
     ;; step x=succ k : (succ k + y = 0) impossible
     (function/lam [['k nat]
                    ['ih (function/arrow (eq-nat (nadd 'k 'y) zero-nat) (eq-nat 'y zero-nat))]]
                   (function/lam [['hs (eq-nat (nadd (succ 'k) 'y) zero-nat)]]
                                 (explode (eq-nat 'y zero-nat)
                                          (function/app (zero-not-successor (nadd 'k 'y))
                                                        (symmetric (nadd (succ 'k) 'y) zero-nat 'hs)))))
     'x))})

;; ---- nat/multiply-succ-zero-left : na*(succ m) = 0 -> na = 0 ----------------
;; nat/multiply recurses on the LEFT: 0*_=0; (succ k)*(succ m) = (succ m)+k*(succ m)
;; = succ(m + k*(succ m)), which is never 0.
(def multiply-succ-zero-left-spec
  {:name 'nat/multiply-succ-zero-left :universes []
   :type (function/forall [['na nat] ['m nat]
                           ['h (eq-nat (nmul 'na (succ 'm)) zero-nat)]]
                          (eq-nat 'na zero-nat))
   :value
   (function/lam
    [['na nat] ['m nat]]
    (nat-rec
     (function/lam [['nv nat]]
                   (function/arrow (eq-nat (nmul 'nv (succ 'm)) zero-nat) (eq-nat 'nv zero-nat)))
     ;; base na=0 : 0*(succ m)=0 -> 0=0
     (function/lam [['h0 (eq-nat (nmul zero-nat (succ 'm)) zero-nat)]] (reflexive-nat zero-nat))
     ;; step na=succ k : (succ k)*(succ m) = (succ m) + k*(succ m) = succ(...) != 0
     (function/lam [['k nat]
                    ['ih (function/arrow (eq-nat (nmul 'k (succ 'm)) zero-nat) (eq-nat 'k zero-nat))]]
                   (function/lam [['hs (eq-nat (nmul (succ 'k) (succ 'm)) zero-nat)]]
                                 (explode (eq-nat (succ 'k) zero-nat)
                                          (function/app
                                           (zero-not-successor (nadd 'm (nmul 'k (succ 'm))))
                                           (symmetric (nmul (succ 'k) (succ 'm)) zero-nat 'hs)))))
     'na))})

;; helper: from h : (a+b) ~ 0, derive na*db + nb*da = 0 (the nat numerator = 0)
(defn- num-sum-zero [a b h]
  ;; S := na*db + nb*da = num(a+b); h : (S)*1 = 0*den(a+b) (defeq), reduce to S = 0
  (let [na (numerator a) nb (numerator b) da (denominator a) db (denominator b)
        S (nadd (nmul na db) (nmul nb da))]
    (transitive S (nmul S (succ zero-nat)) zero-nat
                (symmetric (nmul S (succ zero-nat)) S (mult-one-right S))
                h)))

(def add-zero-split-left-spec
  {:name 'nnrat/add-zero-split-left :universes []
   :type (function/forall [['a nnrat] ['b nnrat] ['h (equiv (radd 'a 'b) nnrat-zero)]]
                          (equiv 'a nnrat-zero))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['h (equiv (radd 'a 'b) nnrat-zero)]]
    (let [na (numerator 'a) db (denominator 'b) nb (numerator 'b) da (denominator 'a)
          S-zero (num-sum-zero 'a 'b 'h)                            ; na*db + nb*da = 0
          nadb-zero (sum-zero-left (nmul na db) (nmul nb da) S-zero) ; na*db = 0
          na-zero (multiply-succ-zero-left na (dpre 'b) nadb-zero)]  ; db = succ(dpre b) -> na = 0
      ;; goal (a ~ 0) reduces to na*1 = 0*da ; provide na*1 = na = 0
      (transitive (nmul na (succ zero-nat)) na zero-nat (mult-one-right na) na-zero)))})

(def add-zero-split-right-spec
  {:name 'nnrat/add-zero-split-right :universes []
   :type (function/forall [['a nnrat] ['b nnrat] ['h (equiv (radd 'a 'b) nnrat-zero)]]
                          (equiv 'b nnrat-zero))
   :value
   (function/lam
    [['a nnrat] ['b nnrat] ['h (equiv (radd 'a 'b) nnrat-zero)]]
    (let [na (numerator 'a) db (denominator 'b) nb (numerator 'b) da (denominator 'a)
          S-zero (num-sum-zero 'a 'b 'h)                             ; na*db + nb*da = 0
          nbda-zero (sum-zero-right (nmul na db) (nmul nb da) S-zero) ; nb*da = 0
          nb-zero (multiply-succ-zero-left nb (dpre 'a) nbda-zero)]   ; da = succ(dpre a) -> nb = 0
      (transitive (nmul nb (succ zero-nat)) nb zero-nat (mult-one-right nb) nb-zero)))})

(def definition-specs [])
(def theorem-specs [sum-zero-right-spec multiply-succ-zero-left-spec
                    add-zero-split-left-spec add-zero-split-right-spec])

(def deps
  "Modules this one installs on top of (see rainbow.module)."
  '[rainbow.math.nat.at-most-cancellation])

(defn install
  "Adds this module's own declarations."
  [checked-environment]
  (-> checked-environment (support/extend-with :nnrat-add-zero-split (concat definition-specs theorem-specs))))

(defn extend-environment [checked-environment]
  (module/install-module checked-environment 'rainbow.math.rational.nnrat.add-zero-split))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
