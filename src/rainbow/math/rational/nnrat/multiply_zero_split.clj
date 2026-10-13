(ns rainbow.math.rational.nnrat.multiply-zero-split
  "nnrat/multiply-zero-split : m1*m2 ~ 0 -> (m1 ~ 0) or (m2 ~ 0). nnrat-equivalent x 0 unfolds to
  (num x)*1 = 0, and num(m1*m2) = (num m1)*(num m2), so the hypothesis strips to (num m1)*(num m2) = 0;
  nat/multiply-zero-split splits it, and each nat disjunct is rebuilt into an nnrat equivalence by the
  same substitution nnrat/square-zero uses. Generalizes nnrat/square-zero to distinct factors."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.multiply-zero-split :as nat-mzs]
            [rainbow.math.nat.semiring :as nat-semiring]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private nnrat (function/const* 'nnrat/NonnegativeRational []))
(def ^:private nat (function/const* 'data/Nat []))
(def ^:private zero (function/const* 'data/zero []))
(defn- succ [n] (function/app (function/const* 'data/succ []) n))
(defn- app [f & a] (apply function/app f a))
(defn- num [m] (app (function/const* 'nnrat/numerator []) m))
(defn- nmul [a b] (app (function/const* 'nat/multiply []) a b))
(defn- mult [a b] (app (function/const* 'nnrat/multiply []) a b))
(def ^:private nnzero (function/const* 'nnrat/zero []))
(defn- nnequiv [a b] (app (function/const* 'nnrat/equivalent []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refln [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- eq-symm [x y h] (app (function/const* 'equality/symmetric [ulvl]) nat x y h))
(defn- eq-trans [x y z h1 h2] (app (function/const* 'equality/transitive [ulvl]) nat x y z h1 h2))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- mult-one-right [x] (app (function/const* 'nat/multiply-one-right []) x))
(defn- nat-mult-zero-split [a b h] (app (function/const* 'nat/multiply-zero-split []) a b h))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))
(defn- use-disj [l r res either onl onr]
  (app (function/const* 'proposition/use-disjunction []) l r res either onl onr))

;; P : t |-> (t*1 = 0); P(num m) is defeq (m ~ 0). Rebuild m~0 from (num m = 0) by transporting
;; P from 0 (where 0*1 = 0 is reflexivity) to num m.
(def ^:private rebuild-motive
  (function/lam [['t nat]] (eqn (nmul 't (succ zero)) zero)))
(defn- rebuild [m hz]
  ;; hz : eqn (num m) zero  ->  nnequiv m nnzero
  (subst zero (num m) (eq-symm (num m) zero hz) rebuild-motive (refln zero)))

(def multiply-zero-split-spec
  {:name 'nnrat/multiply-zero-split
   :universes []
   :type (function/forall [['m1 nnrat] ['m2 nnrat] ['h (nnequiv (mult 'm1 'm2) nnzero)]]
                          (disjt (nnequiv 'm1 nnzero) (nnequiv 'm2 nnzero)))
   :value
   (function/lam
    [['m1 nnrat] ['m2 nnrat] ['h (nnequiv (mult 'm1 'm2) nnzero)]]
    (let [n1 (num 'm1) n2 (num 'm2)
          X (nmul n1 n2)                                    ; num(m1*m2) defeq (num m1)*(num m2)
          m1r (mult-one-right X)                            ; eqn (X*1) X
          ;; h :defeq eqn (X*1) 0 ; strip the *1
          prod0 (eq-trans X (nmul X (succ zero)) zero (eq-symm (nmul X (succ zero)) X m1r) 'h) ; eqn X 0
          split (nat-mult-zero-split n1 n2 prod0)           ; disj (n1=0)(n2=0)
          goal (disjt (nnequiv 'm1 nnzero) (nnequiv 'm2 nnzero))]
      (use-disj (eqn n1 zero) (eqn n2 zero) goal split
                (function/lam [['hl (eqn n1 zero)]]
                              (left-disj (nnequiv 'm1 nnzero) (nnequiv 'm2 nnzero) (rebuild 'm1 'hl)))
                (function/lam [['hr (eqn n2 zero)]]
                              (right-disj (nnequiv 'm1 nnzero) (nnequiv 'm2 nnzero) (rebuild 'm2 'hr))))))})

(def theorem-specs [multiply-zero-split-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      nat-mzs/extend-environment
      nat-semiring/extend-environment
      (support/extend-with :nnrat-multiply-zero-split theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
