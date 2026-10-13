(ns rainbow.math.nat.strict-below-split
  "nat/strict-below-successor-split : strict-below i (succ m) -> (strict-below i m) or (i = m).
  strict-below i n unfolds to (exists extra, (succ i) + extra = n). Eliminate the existence; the
  witness equation succ(i)+extra = succ m gives i+extra = m (successor-injective). Case on extra:
  extra=0 gives i = m (add-commutative strips the +0); extra=succ e gives strict-below i m with
  witness e (add-commutative moves the successor across). The reusable decomposition needed for
  'indexed-max dominates every index below n' -- a pure nat lemma, off the trusted base."
  (:require [rainbow.math.logic.function :as function]
            [rainbow.math.milestone-support :as support]
            [rainbow.math.nat.infinite :as nat-infinite]))

(def ^:private ulvl [:succ [:zero]])
(def ^:private prop-level [:zero])
(def ^:private nat (function/const* 'data/Nat []))
(defn- app [f & a] (apply function/app f a))
(defn- succ [n] (app (function/const* 'data/succ []) n))
(def ^:private nat-zero (function/const* 'data/zero []))
(defn- add [a b] (app (function/const* 'algebra/nat-add []) a b))
(defn- eqn [x y] (app (function/const* 'equality/Eq [ulvl]) nat x y))
(defn- refl [x] (app (function/const* 'equality/reflexive [ulvl]) nat x))
(defn- symm [a b h] (app (function/const* 'equality/symmetric [ulvl]) nat a b h))
(defn- trans [a b c h1 h2] (app (function/const* 'equality/transitive [ulvl]) nat a b c h1 h2))
(defn- subst [x y h P px] (app (function/const* 'equality/substitution [ulvl]) nat x y h P px))
(defn- succ-inj [a b h] (app (function/const* 'nat/successor-injective []) a b h))
(defn- add-comm [a b] (app (function/const* 'nat/add-commutative []) a b))
(defn- strict-below [v u] (app (function/const* 'nat/strict-below []) v u))
(defn- witness [pred value evidence]
  (app (function/const* 'proposition/witness [ulvl]) nat pred value evidence))
(defn- disjt [l r] (app (function/const* 'proposition/disjunction []) l r))
(defn- left-disj [l r h] (app (function/const* 'proposition/left-disjunct []) l r h))
(defn- right-disj [l r h] (app (function/const* 'proposition/right-disjunct []) l r h))

(def strict-below-successor-split-spec
  {:name 'nat/strict-below-successor-split
   :universes []
   :type (function/forall
          [['i nat] ['m nat] ['h (strict-below 'i (succ 'm))]]
          (disjt (strict-below 'i 'm) (eqn 'i 'm)))
   :value
   (function/lam
    [['i nat] ['m nat] ['h (strict-below 'i (succ 'm))]]
    (let [DISJ (disjt (strict-below 'i 'm) (eqn 'i 'm))
          predicate (function/lam [['e-prime nat]] (eqn (add (succ 'i) 'e-prime) 'm))
          motive (function/lam [['ext nat]]
                               (function/arrow (eqn (add 'i 'ext) 'm) DISJ))
          base (function/lam [['e0 (eqn (add 'i nat-zero) 'm)]]
                             (right-disj (strict-below 'i 'm) (eqn 'i 'm)
                                         ;; i = add i 0 = m
                                         (trans 'i (add 'i nat-zero) 'm
                                                (symm (add 'i nat-zero) 'i (add-comm 'i nat-zero))
                                                'e0)))
          stepfn (function/lam
                  [['e nat] ['ih (function/arrow (eqn (add 'i 'e) 'm) DISJ)]]
                  (function/lam
                   [['es (eqn (add 'i (succ 'e)) 'm)]]
                   (let [;; add i (succ e) ~ succ(add e i) (add-commutative; add (succ e) i defeq succ(add e i))
                         comm1 (add-comm 'i (succ 'e))                       ; eqn (add i (succ e)) (succ(add e i))
                         se-m (trans (succ (add 'e 'i)) (add 'i (succ 'e)) 'm
                                     (symm (add 'i (succ 'e)) (succ (add 'e 'i)) comm1)
                                     'es)                                    ; eqn (succ(add e i)) m
                         cong (subst (add 'e 'i) (add 'i 'e) (add-comm 'e 'i)
                                     (function/lam [['t nat]] (eqn (succ (add 'e 'i)) (succ 't)))
                                     (refl (succ (add 'e 'i))))              ; eqn (succ(add e i)) (succ(add i e))
                         evidence (trans (succ (add 'i 'e)) (succ (add 'e 'i)) 'm
                                         (symm (succ (add 'e 'i)) (succ (add 'i 'e)) cong)
                                         se-m)]                              ; eqn (succ(add i e)) m = eqn (add (succ i) e) m
                     (left-disj (strict-below 'i 'm) (eqn 'i 'm)
                                (witness predicate 'e evidence)))))]
      (app 'h DISJ
           (function/lam
            [['extra nat] ['pf (eqn (add (succ 'i) 'extra) (succ 'm))]]
            (app (function/app (function/const* 'data/Nat.rec [prop-level]) motive base stepfn 'extra)
                 (succ-inj (add 'i 'extra) 'm 'pf))))))})

(def theorem-specs [strict-below-successor-split-spec])

(defn extend-environment [checked-environment]
  (-> checked-environment
      nat-infinite/extend-environment
      (support/extend-with :nat-strict-below-split theorem-specs)))

(defn theorem-ids [checked-environment]
  (support/spec-ids checked-environment theorem-specs))
