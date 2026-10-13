(ns rainbow.math.rational.nnrat.add-cancel-zero
  "Additive cancellation to zero for nonnegative rationals:

    nnrat/add-cancel-to-zero : (a + g) ~ a  ->  g ~ 0

  If adding g changes nothing, g was 0.  The extraction step for complementary
  slackness: a zero duality gap means the objective is unchanged by the slack
  term, so the slack term is 0.

  Proof: (a+g) ~ a unfolds (denominator-combine reduces) to the nat identity
  (na*dg + ng*da)*da = na*(da*dg); nat-ring isolates it to X + ng*da*da = X, so
  nat/add-left-cancel gives ng*da*da = 0, and da = succ _ positive lets
  multiply-succ-zero-left (applied twice) conclude ng = 0, i.e. g ~ 0.
  Native and axiom-free; chains nnrat-add-zero-split (for multiply-succ-zero-left)
  and nat-ring on d63."
  (:refer-clojure :exclude [numerator denominator])
  (:require [rainbow.math.milestone-support :as support]
            [rainbow.math.logic.function :as function]
            [rainbow.math.nat.ring :as ring]
            [rainbow.math.rational.nnrat.add-zero-split :as zs]))

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
(defn- mult-one-right [v] (function/app (function/const* 'nat/multiply-one-right []) v))
(defn- add-zero-right [v] (function/app (function/const* 'algebra/nat-add-zero-right []) v))
(defn- add-left-cancel [k a b h]
  (function/app (function/const* 'nat/add-left-cancel []) k a b h))
(defn- multiply-succ-zero-left [na m h]
  (function/app (function/const* 'nat/multiply-succ-zero-left []) na m h))
(defn- ring-eq [l r] (:proof (ring/prove-nat-eq l r)))

(def add-cancel-to-zero-spec
  {:name 'nnrat/add-cancel-to-zero :universes []
   :type (function/forall [['a nnrat] ['g nnrat] ['h (equiv (radd 'a 'g) 'a)]]
                          (equiv 'g nnrat-zero))
   :value
   (function/lam
    [['a nnrat] ['g nnrat] ['h (equiv (radd 'a 'g) 'a)]]
    (let [na (numerator 'a) ng (numerator 'g)
          da (denominator 'a) dg (denominator 'g) dpa (dpre 'a)
          ;; h : (na*dg + ng*da)*da = na*(da*dg)   [equiv (a+g) a unfolds; den(a+g)->da*dg]
          LHS0 (nmul (nadd (nmul na dg) (nmul ng da)) da)
          RHS0 (nmul na (nmul da dg))
          X (nmul (nmul na dg) da)          ; na*dg*da
          Y (nmul (nmul ng da) da)          ; (ng*da)*da
          ;; (X+Y) = LHS0 = RHS0 = X
          hXY (transitive (nadd X Y) LHS0 X
                          (symmetric LHS0 (nadd X Y) (ring-eq LHS0 (nadd X Y)))
                          (transitive LHS0 RHS0 X 'h (ring-eq RHS0 X)))
          ;; X+Y = X+0 -> Y = 0
          hX0 (transitive (nadd X Y) X (nadd X zero-nat)
                          hXY (symmetric (nadd X zero-nat) X (add-zero-right X)))
          Y-zero (add-left-cancel X Y zero-nat hX0)             ; (ng*da)*da = 0
          ngda-zero (multiply-succ-zero-left (nmul ng da) dpa Y-zero) ; da=succ dpa -> ng*da = 0
          ng-zero (multiply-succ-zero-left ng dpa ngda-zero)]   ; -> ng = 0
      ;; goal (g ~ 0) reduces to ng*1 = 0*dg ; provide ng*1 = ng = 0
      (transitive (nmul ng (succ zero-nat)) ng zero-nat (mult-one-right ng) ng-zero)))})

(def definition-specs [])
(def theorem-specs [add-cancel-to-zero-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      zs/extend-environment
      (support/extend-with :nnrat-add-cancel-zero
                           (concat definition-specs theorem-specs))))
(defn definition-ids [checked-environment]
  (support/spec-ids checked-environment definition-specs))
(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
